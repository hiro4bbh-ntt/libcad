#include <cstdint>

typedef struct {
  uint64_t id;
} SingleInheritClass;

typedef struct {
  SingleInheritClass h;
  uint8_t b;
} SingleInheritClass1;

typedef struct {
  SingleInheritClass h;
  int32_t i;
} SingleInheritClass2;

#define SINGLE_INHERIT_CLASS_ID_1 1
#define SINGLE_INHERIT_CLASS_ID_2 2
