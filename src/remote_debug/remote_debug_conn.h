#ifndef REMOTE_DEBUG_CONN_H
#define REMOTE_DEBUG_CONN_H

struct rconn;

enum ConnectionType
{
    ConnectionType_Listener,
    ConnectionType_Connect
};

struct rconn* rconn_create (enum ConnectionType type, int port);
void rconn_destroy (struct rconn* conn);

void rconn_update_listner (struct rconn* conn);
int rconn_is_connected (struct rconn* conn);

int rconn_send(struct rconn* conn, const void* buffer, int length, int flags);
int rconn_recv (struct rconn* conn, char* buffer, int length, int flags);

int rconn_poll_read(struct rconn* conn);

#endif
