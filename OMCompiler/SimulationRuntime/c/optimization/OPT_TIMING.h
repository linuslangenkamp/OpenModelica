#ifndef IPOPT_TIMING_H
#define IPOPT_TIMING_H

#include <stdio.h>
#include <sys/time.h>

#ifdef __cplusplus
extern "C" {
#endif

extern double ipopt_time;
extern double ipopt_eval_f_time;
extern double ipopt_eval_grad_f_time;
extern double ipopt_eval_g_time;
extern double ipopt_eval_jac_g_time;
extern double ipopt_eval_hessian_time;
extern double get_wall_time();

static inline double ipopt_begin_timing() {
    return get_wall_time();
}

static inline void ipopt_end_timing(double start, double *accumulator) {
    double end = get_wall_time();
    *accumulator += (end - start);
}

static inline void print_ipopt_callback_times(void) {
    double total = ipopt_eval_f_time + ipopt_eval_grad_f_time + ipopt_eval_g_time + ipopt_eval_jac_g_time + ipopt_eval_hessian_time;
    printf("Total                              : %.6f sec\n", ipopt_time);
    printf("Total time MUMPS and Ipopt         : %.6f sec\n", ipopt_time - total);
    printf("Total IPOPT callback time          : %.6f sec\n", total);
    printf(" - Objective eval (eval_f)         : %.6f sec\n", ipopt_eval_f_time);
    printf(" - Gradient eval (eval_grad_f)     : %.6f sec\n", ipopt_eval_grad_f_time);
    printf(" - Constraint eval (eval_g)        : %.6f sec\n", ipopt_eval_g_time);
    printf(" - Jacobian eval (eval_jac_g)      : %.6f sec\n", ipopt_eval_jac_g_time);
    printf(" - Hessian eval (eval_hessian_lag) : %.6f sec\n", ipopt_eval_hessian_time);

}

#ifdef __cplusplus
}
#endif

#endif // IPOPT_TIMING_H
