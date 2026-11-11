#include "closure_call.h"

struct closure {
  value (*func)(struct thread_info *, value, value);
  value env;
};

value closure_call(struct thread_info *$tinfo, value $clo, value $arg)
{
  register value (*$f)(struct thread_info*, value, value);
  register value $envi;
  register value $tmp;
  $f = (*((struct closure *) $clo)).func;
  $envi = (*((struct closure *) $clo)).env;
  $tmp = $f($tinfo, $envi, $arg);
  return $tmp;
}
