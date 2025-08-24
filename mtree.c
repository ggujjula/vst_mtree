
typedef enum mtree_node_type {
    LEAF = 0,
    INTERNAL = 1,
//    MAX = 2,
} mtree_node_type;

typedef struct mtree_node {
    mtree_node_type type;
    union {
        void *data;
        struct mtree_node *children;
    };
} mtree_node;