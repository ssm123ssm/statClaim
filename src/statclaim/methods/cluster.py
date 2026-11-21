"""Tests for cluster-randomised trials. Guarantees are cited, not proved.

These tests take one summary per cluster, such as its mean outcome, so the sample size
is the number of clusters. They need cluster_assignment(...). The references await the
user's review and are marked "to verify".
"""

from statclaim.methods.assumptions import (
    FIXED_SIZES,
    INDEPENDENT_CLUSTERS,
    NORMAL_CLUSTER_PROPORTIONS,
    NORMAL_CLUSTER_SUMMARIES,
    SINGLE_ANALYSIS,
)
from statclaim.methods.core import CitedMethod, MethodModule
from statclaim.methods.power import CLUSTER_MEANS, CLUSTER_PROPORTIONS
from statclaim.methods.simulation import CLUSTER_MEANS as CLUSTER_MEANS_SIMULATED
from statclaim.methods.simulation import CLUSTER_PROPORTIONS as CLUSTER_PROPORTIONS_SIMULATED

TO_VERIFY = " [to verify]"
DONNER_KLAR = (
    "Donner, A. and Klar, N. (2000). Design and Analysis of Cluster Randomization Trials in "
    "Health Research. Arnold, London." + TO_VERIFY
)
HAYES_MOULTON = (
    "Hayes, R. J. and Moulton, L. H. (2017). Cluster Randomised Trials, 2nd ed. Chapman and "
    "Hall/CRC, Boca Raton." + TO_VERIFY
)

MODULE = MethodModule(
    "tests.cluster",
    "The t-test on cluster-level summaries for a cluster-randomised trial: one value per "
    "cluster, a mean or a proportion of responders, with the clusters as the sample size. It "
    "needs cluster_assignment and at least four clusters per arm. The Type I guarantee is "
    "cited, exact if the cluster summaries are normal with a common variance, and not checked "
    "by Lean. Power comes from the noncentral t, given the intracluster correlation. For a "
    "proved analysis, use randomisation_test.",
    (
        CitedMethod(
            key="cluster_t_test",
            module="tests.cluster",
            title="Two-sided t-test on cluster-level summaries",
            version=1,
            outcome="continuous",
            null="equal_means",
            relation="equals",
            scope="finite_sample",
            assumptions=(
                INDEPENDENT_CLUSTERS,
                FIXED_SIZES,
                SINGLE_ANALYSIS,
                NORMAL_CLUSTER_SUMMARIES,
            ),
            references=(DONNER_KLAR, HAYES_MOULTON),
            # Counted in clusters. With fewer, a cluster-level analysis has little power and
            # the normality of summaries cannot be judged.
            min_per_arm=4,
            min_total=8,
            unit="cluster",
            power=CLUSTER_MEANS,
            simulation=CLUSTER_MEANS_SIMULATED,
        ),
        # The same test on each cluster's proportion of responders. Its null compares the
        # mean cluster proportions, which equal the arms' response rates under the model.
        CitedMethod(
            key="cluster_proportion_t_test",
            module="tests.cluster",
            title="Two-sided t-test on cluster proportions",
            version=1,
            outcome="binary",
            null="equal_proportions",
            relation="equals",
            scope="finite_sample",
            assumptions=(
                INDEPENDENT_CLUSTERS,
                FIXED_SIZES,
                SINGLE_ANALYSIS,
                NORMAL_CLUSTER_PROPORTIONS,
            ),
            references=(DONNER_KLAR, HAYES_MOULTON),
            min_per_arm=4,
            min_total=8,
            unit="cluster",
            power=CLUSTER_PROPORTIONS,
            simulation=CLUSTER_PROPORTIONS_SIMULATED,
        ),
    ),
)
