#ifndef TEST_MODEL_FIXTURE_H
#define TEST_MODEL_FIXTURE_H

#include <expr/expr.hh>

/* yasmv holds one model per process, so the tests that need a model
   share this one. Whichever test runs first builds it, which keeps the
   tests independent of their order. Module `main` declares a pair of
   variables for each type: (x, y) are booleans, (s, t) are
   unsigned(16) and (u, v) are signed(16). The word width is 16 bits. */
struct ModelFixture {
    ModelFixture();

    expr::Expr_ptr x, y, s, t, u, v;

    /* whether the model passed analysis */
    bool analyzed;
};

#endif /* TEST_MODEL_FIXTURE_H */
