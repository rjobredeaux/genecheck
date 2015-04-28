
#ifndef __simple_olg__
#define __simple_olg__

/* Includes */

#include "simple_olg_types.h"
#include "GATypes.h"


/* Variable Declarations */

extern REAL simple_olg_yd;
extern REAL simple_olg_y;

/* Function prototypes */

extern void simple_olg_init(t_simple_olg_state *_state_);
extern void simple_olg_compute(t_simple_olg_io *_io_, t_simple_olg_state *_state_);


#endif
