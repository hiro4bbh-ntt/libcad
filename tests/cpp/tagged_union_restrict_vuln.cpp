#include "./tagged_union.hpp"

ContextInline *alloc_context_inline(Closure *cl)
{
  ContextInline *ctx = new ContextInline;
  ctx->cl.v.cl = cl;
  object_set_tag(&ctx->cl, OBJECT_ID_BYTE);
  ctx->ncalls.v.b = 0;
  object_set_tag(&ctx->ncalls, OBJECT_ID_CLOSURE);
  return ctx;
}
