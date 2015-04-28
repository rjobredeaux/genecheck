
#ifndef __simple_olg_types__
#define __simple_olg_types__

/* Includes */

#include "simple_olg.h"
#include "GATypes.h"


/* Type declarations */

typedef struct {
    REAL yd;
    REAL y;
    REAL u;
} t_simple_olg_io;

typedef struct {
    REAL Integrator_1_memory;
    REAL Integrator_2_memory;
} t_simple_olg_state;



#endif
