#include <cstdint>

typedef struct {
  uint64_t len, cap;
  uint8_t *buf;
} String;

typedef struct {
  int (*fnptr)(void *env, void *arg);
  void *env;
} Closure;

typedef struct {
  uint64_t h;
  union {
    uint8_t b;
    int32_t i;
    double d;
    String *str;
    Closure *cl;
  } v;
} Object;

#define OBJECT_ID_NIL     0
#define OBJECT_ID_FALSE   1
#define OBJECT_ID_TRUE    2
#define OBJECT_ID_BYTE    3
#define OBJECT_ID_INT     4
#define OBJECT_ID_LONG    5
#define OBJECT_ID_FLOAT   6
#define OBJECT_ID_STRING  7
#define OBJECT_ID_CLOSURE 8

#define object_get_tag(o) \
  ((o)->h)
#define object_set_tag(o, t) \
  (o)->h = (t)

#define object_is_true(o) \
  (object_get_tag(o) == OBJECT_ID_TRUE)
#define object_is_byte(o) \
  (object_get_tag(o) == OBJECT_ID_BYTE)
#define object_is_int(o) \
  (object_get_tag(o) == OBJECT_ID_INT)
#define object_is_closure(o) \
  (object_get_tag(o) == OBJECT_ID_CLOSURE)

#define object_get_closure(o) \
  ((o)->v.cl)

int object_inc_byte(Object *obj)
{
  if (object_is_byte(obj)) {
    return obj->v.b + 1;
  }
  return -1;
}

typedef struct {
  Object key;
  Object value;
} KeyValue;

typedef struct {
  Object cl;
  Object ncalls;
} ContextInline;
