// From Chandra et al. (1999) "Physical type checking for C." PASTE.
// Example in Section 3.3.
struct Point {
  int x, y;
};

struct ColorPoint {
  int x, y;
  int color;
};

struct PointObject {
  int tag;
  Point *p;
};

struct ColorPointObject {
  int tag;
  ColorPoint *cp;
};

ColorPointObject f(ColorPointObject cpo) {
  cpo.cp->x = 0;
  return cpo;
}

int main(void)
{
  Point p;
  ColorPointObject cpo;
  PointObject *pop = (PointObject *) &cpo;
  ColorPointObject *cpop = &cpo;
  Point *q = &p;
  pop->p = q;
  ColorPoint *cp = cpop->cp;
  cp->color = 1;
  return 0;
}