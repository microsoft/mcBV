module GlobalOptions


// Global flags like debug and possibly other options we might want to add over time
let mutable TRC = false
let mutable DBG = false
let mutable VRB = false //Verbose
let mutable PREPROCESS = true
let mutable SHOWMODEL = false
let mutable RUNZ3CHECKS = false // Default: disabled
let mutable VERIFYMODEL = false // Default: enabled
let mutable POLITE = false //Default: disabled
let mutable GENERALIZE = true
let mutable SHOW_CONFLICTS = false

let mutable BV_SEGMENT_STRING_LIMIT = 4;

let mutable USE_BOUNDS = true

#if INTERACTIVE
let mutable INTERACTIVE = true
#else
let mutable INTERACTIVE = false
#endif
