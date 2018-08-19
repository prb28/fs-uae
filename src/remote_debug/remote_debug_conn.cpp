#include "remote_debug_conn.h"
#include <string.h>
#include <stdint.h>
#include <stdio.h>
#if defined(_MSC_VER)
#pragma warning(disable: 4496)
#include <winsock2.h>
#pragma warning(default: 4496)
#include <winsock2.h>
#include <Ws2tcpip.h>
#endif

#if defined(WINDOWS)
#include <ws2tcpip.h>
#endif
#if !defined(_WIN32)
#include <sys/types.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include <arpa/inet.h>
#endif

#if defined(__linux__)
#include <sys/time.h>
#endif

#ifndef INVALID_SOCKET
#define INVALID_SOCKET -1
#endif

#if !defined(_WIN32)
#define closesocket close
#endif

#include "sysconfig.h"
#include "sysdeps.h"

// hack
extern bool need_ack;

typedef struct rconn
{
    enum ConnectionType type;

    SOCKET server_socket;     // used when having a listener socket
    SOCKET socket;

} rconn;

void debug_log (const char* fmt, ...)
{
#ifdef DEBUG_LOG
    va_list args;
    va_start(args, fmt);
    vfprintf(stderr, fmt, args);
    va_end(args);
#else
    (void)fmt;
#endif
}

static int socket_poll (int socket)
{
    struct timeval to = { 0, 0 };
    fd_set fds;

    FD_ZERO(&fds);

#ifdef _MSC_VER
#pragma warning(push)
#pragma warning(disable: 4127)
#endif
    FD_SET(socket, &fds);
#ifdef _MSC_VER
#pragma warning(pop)
#endif

    return select (socket + 1, &fds, NULL, NULL, &to) > 0;
}

static int create_listner (rconn* conn, int port)
{
    struct sockaddr_in sin;
    int yes = 1;

    conn->server_socket = (int)socket (AF_INET, SOCK_STREAM, 0);

    if (conn->server_socket == INVALID_SOCKET)
        return 0;

    memset(&sin, 0, sizeof sin);

    sin.sin_family = AF_INET;
    sin.sin_addr.s_addr = INADDR_ANY;
    sin.sin_port = htons((unsigned short)port);

    if (setsockopt (conn->server_socket, SOL_SOCKET, SO_REUSEADDR, (const char*)&yes, sizeof(int)) == -1) {
        perror("setsockopt");
        return 0;
    }

    if (-1 == bind (conn->server_socket, (struct sockaddr*)&sin, sizeof(sin))) {
        perror("bind");
        return 0;
    }

    while (listen(conn->server_socket, SOMAXCONN) == -1)
        ;

    debug_log("created listener\n");

    return 1;
}

struct rconn* rconn_create (enum ConnectionType type, int port)
{
    rconn* conn = 0;

#if defined(_WIN32)
    WSADATA wsaData;
    if (WSAStartup(MAKEWORD(2, 0), &wsaData) != 0)
        return 0;
#endif

    conn = xmalloc(struct rconn, 1);

    conn->type = type;
    conn->server_socket = INVALID_SOCKET;
    conn->socket = INVALID_SOCKET;

    if (type == ConnectionType_Listener) {
        if (!create_listner(conn, port)) {
            xfree(conn);
            return 0;
        }
    }

    return conn;
}

void rconn_destroy (struct rconn* conn)
{
    if (!conn)
            return;

    if (conn->socket != INVALID_SOCKET)
        closesocket(conn->socket);

    if (conn->server_socket != INVALID_SOCKET)
        closesocket(conn->server_socket);

    xfree(conn);
}

static int rconn_connected (struct rconn* conn)
{
    return conn->socket != INVALID_SOCKET;
}

static int client_connect (rconn* conn, struct sockaddr_in* host)
{
    struct sockaddr_in hostTemp;
    unsigned int hostSize = sizeof(struct sockaddr_in);

    debug_log("Trying to accept\n");

    conn->socket = (int)accept (conn->server_socket, (struct sockaddr*)&hostTemp, (socklen_t*)&hostSize);

    if (INVALID_SOCKET == conn->socket) {
        perror("accept");
        debug_log("Unable to accept connection..\n");
        return 0;
    }

    if (NULL != host)
        *host = hostTemp;

    // If we got an connection we need to switch to tracing mode directly as this is required by gdb

    debug_log("Accept done\n");

    return 1;
}

int rconn_is_connected (rconn* conn)
{
    if (conn == NULL)
        return 0;

    return conn->socket != INVALID_SOCKET;
}

void rconn_update_listner (rconn* conn)
{
    struct timeval timeout;
    struct sockaddr_in client;
    fd_set fds;

    FD_ZERO(&fds);

#ifdef _MSC_VER
#pragma warning(push)
#pragma warning(disable: 4127)
#endif
    FD_SET (conn->server_socket, &fds);
#ifdef _MSC_VER
#pragma warning(pop)
#endif

    timeout.tv_sec = 0;
    timeout.tv_usec = 0;

    if (rconn_is_connected (conn))
        return;

    // look for new clients

    if (select (conn->server_socket + 1, &fds, NULL, NULL, &timeout) > 0)
    {
        if (client_connect (conn, &client))
            debug_log ("Connected to %s\n", inet_ntoa(client.sin_addr));
    }
}

static int rconn_disconnect (rconn* conn)
{
    debug_log("Disconnected\n");

    // reset the ack mode if client disconnected
    need_ack = true;

    if (conn->socket != INVALID_SOCKET)
        closesocket(conn->socket);

    debug_log("set invalid socket\n");

    conn->socket = INVALID_SOCKET;

    return 1;
}

int rconn_recv (rconn* conn, char* buffer, int length, int flags)
{
    int ret;

    if (!rconn_connected(conn))
        return 0;

    ret = (int)recv(conn->socket, buffer, (size_t)length, flags);

    debug_log("recv %d\n", ret);

    if (ret <= 0)
    {
        debug_log("recv %d %d\n", ret, length);
        rconn_disconnect(conn);
        return 0;
    }

    return ret;
}

int rconn_send(rconn* conn, const void* buffer, int length, int flags)
{
    int ret;

    if (!rconn_connected(conn))
        return 0;

#if 0
        printf("About to send\n");

        char* c = (char*)buffer;

        for (int i = 0; i < length; ++i)
                printf("%c", c[i]);

        printf("\n");
#endif

#ifdef FSUAE
    if ((ret = (int)send(conn->socket, (char*)buffer, (size_t)length, flags)) != (int)length)
#else
    if ((ret = (int)send(conn->socket, (char*)buffer, (size_t)length, flags)) != (int)length)
#endif
    {
        printf("disconnected because length doesn't match (expected %d but got %d)\n", length, ret);
        rconn_disconnect(conn);
        return 0;
    }

    // take a copy of what we sent last if we need to resend it

    //memcpy (s_lastSent, buffer, length);
    //s_lastSize = 0;

    return ret;
}

int rconn_poll_read(rconn* conn)
{
    if (!rconn_connected(conn))
        return 0;

    return !!socket_poll(conn->socket);
}



