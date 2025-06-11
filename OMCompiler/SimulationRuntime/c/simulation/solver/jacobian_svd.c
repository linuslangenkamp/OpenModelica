#include "jacobian_svd.h"

// LAPACK dense SVD routine
extern void dgesvd_(char* jobu, char* jobvt, int* m, int* n,
                    modelica_real* a, int* lda, modelica_real* s,
                    modelica_real* u, int* ldu, modelica_real* vt, int* ldvt,
                    modelica_real* work, int* lwork, int* info);

static SVD_DATA* svd_create(SPARSE_PATTERN* sparse_pattern, modelica_real* values, int rows, int cols)
{
    SVD_DATA* svd_data = calloc(1, sizeof(SVD_DATA));
    if (!svd_data) return NULL;

    svd_data->rows           = rows;
    svd_data->cols           = cols;
    svd_data->sparse_pattern = sparse_pattern;
    svd_data->sp_values      = values;
    svd_data->min_rows_cols  = rows < cols ? rows : cols;

    svd_data->A_dense = calloc(rows * cols, sizeof(modelica_real));

    // for now, create dense matrix from sparse CSC
    if (sparse_pattern)
    {
        unsigned int* lead = sparse_pattern->leadindex;
        unsigned int* index = sparse_pattern->index;

        for (int column = 0; column < cols; column++)
        {
            for (unsigned int nz = lead[column]; nz < lead[column + 1]; nz++)
            {
                unsigned int row = index[nz];
                svd_data->A_dense[column * rows + row] = values[nz];
            }
        }
    }
    else
    {
        memcpy(svd_data->A_dense, values, rows * cols * sizeof(modelica_real));
    }

    // allocate SVD result buffers
    svd_data->S = malloc(svd_data->min_rows_cols * sizeof(modelica_real));
    svd_data->U = malloc(rows * rows * sizeof(modelica_real));
    svd_data->VT = malloc(cols * cols * sizeof(modelica_real));

    return svd_data;
}

static void svd_free(SVD_DATA* svd_data)
{
    if (!svd_data) return;
    free(svd_data->A_dense);
    free(svd_data->S);
    free(svd_data->U);
    free(svd_data->VT);
    free(svd_data);
}


static int svd_compute_lapack(SVD_DATA* svd_data)
{
    int rows = svd_data->rows;
    int cols = svd_data->cols;
    int lda = rows;
    int ldu = rows;
    int ldvt = cols;
    int info;
    char jobu = 'A';
    char jobvt = 'A';

    // workspace query
    int lwork = -1;
    modelica_real wkopt;
    dgesvd_(&jobu, &jobvt, &rows, &cols,
            svd_data->A_dense, &lda,
            svd_data->S, svd_data->U, &ldu, svd_data->VT, &ldvt,
            &wkopt, &lwork, &info);

    if (info != 0) return info;

    lwork = (int)wkopt;
    modelica_real* work = malloc(sizeof(modelica_real) * lwork);

    // actual SVD
    dgesvd_(&jobu, &jobvt, &rows, &cols,
            svd_data->A_dense, &lda,
            svd_data->S, svd_data->U, &ldu, svd_data->VT, &ldvt,
            work, &lwork, &info);
    return 0;
}

static void svd_calculate_statistics(SVD_DATA* svd_data)
{
    // condition statistics
    svd_data->sigma_max = svd_data->S[0];
    svd_data->sigma_min = svd_data->S[svd_data->min_rows_cols - 1];
    svd_data->cond = svd_data->sigma_min > 0.0 ? svd_data->sigma_max / svd_data->sigma_min : INFINITY;

    // rank estimation
    svd_data->estimated_rank = 0;
    svd_data->rank_est_tol = __max(svd_data->rows, svd_data->cols) * DBL_EPSILON * svd_data->sigma_max;
    for (int dim = 0; dim < svd_data->min_rows_cols; dim++)
    {
        if (svd_data->S[dim] > svd_data->rank_est_tol)
        {
            svd_data->estimated_rank++;
        }
    }

    // binary search to find first singular value < threshold
    modelica_real sigma_max = svd_data->S[0];
    modelica_real threshold = 0.01 * sigma_max;

    int low = 0;
    int high = svd_data->min_rows_cols - 1;
    int first_below = svd_data->min_rows_cols;

    while (low <= high)
    {
        int mid = (low + high) / 2;
        if (svd_data->S[mid] < threshold)
        {
            first_below = mid;
            high = mid - 1;
        }
        else
        {
            low = mid + 1;
        }
    }
    svd_data->least_one_percent = first_below;
}

static void svd_dump_statistics(const SVD_DATA* svd_data)
{
    if (!svd_data || !svd_data->S) {
        infoStreamPrint(OMC_LOG_NLS_SVD, 1, "No SVD data available.");
        messageClose(OMC_LOG_NLS_SVD);
        return;
    }
    else
    {
        infoStreamPrint(OMC_LOG_NLS_SVD, 1, "Starting SVD analysis.");
        messageClose(OMC_LOG_NLS_SVD);
    }

    // condition number
    infoStreamPrint(OMC_LOG_NLS_SVD, 1, "Matrix condition");
    infoStreamPrint(OMC_LOG_NLS_SVD, 0, "Cond(M) = %.5e", svd_data->cond);
    if (svd_data->cond > 1e12)
    {
        infoStreamPrint(OMC_LOG_NLS_SVD, 0, "Matrix is very ill-conditioned: 1e12 < Cond(M) = %.5e", svd_data->cond);
    }
    else if (svd_data->cond > 1e8)
    {
        infoStreamPrint(OMC_LOG_NLS_SVD, 0, "Matrix is fairly ill-conditioned: 1e8 < Cond(M) = %.5e < 1e12", svd_data->cond);
    }
    else if (svd_data->cond > 1e4)
    {
        infoStreamPrint(OMC_LOG_NLS_SVD, 0, "Matrix is moderately ill-conditioned: 1e4 < Cond(M) = %.5e < 1e8", svd_data->cond);
    }
    else
    {
        infoStreamPrint(OMC_LOG_NLS_SVD, 0, "Matrix is well conditioned: Cond(M) = %.5e < 1e4", svd_data->cond);
    }
    messageClose(OMC_LOG_NLS_SVD);

    // singular values
    infoStreamPrint(OMC_LOG_NLS_SVD, 1, "Singular values");
    for (int i = 0; i < svd_data->min_rows_cols; i++)
    {
        infoStreamPrint(OMC_LOG_NLS_SVD, 0, "sigma_%-3d =  %.5e", i + 1, svd_data->S[i]);
    }
    messageClose(OMC_LOG_NLS_SVD);

    // rank estimation
    infoStreamPrint(OMC_LOG_NLS_SVD, 1, "Rank estimation");
    infoStreamPrint(OMC_LOG_NLS_SVD, 0, "estimated = %d", svd_data->estimated_rank);
    infoStreamPrint(OMC_LOG_NLS_SVD, 0, "actual    = %d", svd_data->min_rows_cols);
    infoStreamPrint(OMC_LOG_NLS_SVD, 0, "estimation tolerance = %.5e", svd_data->rank_est_tol);
    if (svd_data->estimated_rank < svd_data->min_rows_cols)
    {
        infoStreamPrint(OMC_LOG_NLS_SVD, 0, "Matrix may be rank-deficient.");
    }
    else
    {
        infoStreamPrint(OMC_LOG_NLS_SVD, 0, "Matrix should have full rank.");
    }
    messageClose(OMC_LOG_NLS_SVD);

    // print right singular vectors for singular values below 1% of sigma_max
    infoStreamPrint(OMC_LOG_NLS_SVD, 1, "Smallest right singular vectors");

    if (svd_data->least_one_percent == svd_data->min_rows_cols)
    {
        infoStreamPrint(OMC_LOG_NLS_SVD, 0, "No singular values below %.5e (1%% of max)", 0.01 * svd_data->sigma_max);
    }
    else
    {
        int start = svd_data->min_rows_cols - 1;
        int end = svd_data->least_one_percent;
        int count = start - end + 1;

        infoStreamPrint(OMC_LOG_NLS_SVD, 0,
            "Found %d singular %s below %.5e (1%% of sigma_max)", count, count > 1 ? "values" : "value", 0.01 * svd_data->sigma_max);

        for (int v = start; v >= end; v--)
        {
            infoStreamPrint(OMC_LOG_NLS_SVD, 1, "V[%d] (singular value %.5e)", v + 1, svd_data->S[v]);
            for (int i = 0; i < svd_data->cols; i++)
            {
                modelica_real v_entry = svd_data->VT[v * svd_data->cols + i];
                infoStreamPrint(OMC_LOG_NLS_SVD, 0, "V[%d][%d] = %.5e", v + 1, i + 1, v_entry);
            }
            messageClose(OMC_LOG_NLS_SVD);  // close after each vector print block
        }
    }
    messageClose(OMC_LOG_NLS_SVD);

    infoStreamPrint(OMC_LOG_NLS_SVD, 1, "SVD analysis complete.");
    messageClose(OMC_LOG_NLS_SVD);
}

int svd_compute(SPARSE_PATTERN* sparse_pattern, modelica_real* values, int rows, int cols)
{
    SVD_DATA* svd_data = svd_create(sparse_pattern, values, rows, cols);
    svd_compute_lapack(svd_data);
    svd_calculate_statistics(svd_data);
    svd_dump_statistics(svd_data);
    svd_free(svd_data);

    return 0;
}
