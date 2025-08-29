#include <stdlib.h>
#include <stdio.h>
#include <openssl/evp.h>

typedef enum mtree_node_type {
    LEAF = 0,
    INTERNAL = 1,
//    MAX = 2,
} mtree_node_type;

typedef struct mtree_node {
    size_t refcount;
    mtree_node_type type;
    unsigned char hash[EVP_MAX_MD_SIZE];
    unsigned int hash_len;
    union {
        struct {
            void *data;
            size_t len;
        };
        struct mtree_node *children;
    };
} mtree_node;

int produce_hash(void *data, size_t len, unsigned char hash[EVP_MAX_MD_SIZE], unsigned int *hash_len);

mtree_node *mtree_child(void *data, size_t len) {
    mtree_node *node = malloc(sizeof (mtree_node));
    if (node == NULL) {
        return NULL;
    }
    node->refcount = 1;
    node->type = LEAF;
    if (produce_hash(data, len, (node->hash), &(node->hash_len)) != 0) {
        fprintf(stderr, "Failed to produce hash\n");
        free(node);
        return NULL;
    }
    node->data = data;
    node->len = len;
    return node;
}

int produce_hash(void *data, size_t len, unsigned char hash[EVP_MAX_MD_SIZE], unsigned int *hash_len) {
    // Context for digest operations
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    if (!ctx) {
        fprintf(stderr, "Failed to create EVP_MD_CTX\n");
        return 1;
    }

    // Initialize digest operation for SHA1
    if (EVP_DigestInit_ex(ctx, EVP_sha1(), NULL) != 1) {
        fprintf(stderr, "DigestInit failed\n");
        EVP_MD_CTX_free(ctx);
        return 1;
    }

    // Supply the data
    if (EVP_DigestUpdate(ctx, data, len) != 1) {
        fprintf(stderr, "DigestUpdate failed\n");
        EVP_MD_CTX_free(ctx);
        return 1;
    }

    // Finalize and get the hash
    if (EVP_DigestFinal_ex(ctx, hash, hash_len) != 1) {
        fprintf(stderr, "DigestFinal failed\n");
        EVP_MD_CTX_free(ctx);
        return 1;
    }

    EVP_MD_CTX_free(ctx);

    return 0;
}

int main (void) {
    return 0;
}