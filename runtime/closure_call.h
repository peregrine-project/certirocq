#ifndef CLOSURE_CALL_H
#define CLOSURE_CALL_H

#include "values.h"
#include "gc_stack.h"

/* Apply a CertiRocq closure to one argument: [clo] points to a pair of a code
   pointer and an environment.  Used by certirocq_gmp.c. */
value closure_call(struct thread_info *, value, value);

#endif /* CLOSURE_CALL_H */
