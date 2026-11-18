"""Kinds of two-arm outcome and the null hypotheses that can be stated about each.

To support a new kind of endpoint, add an Outcome here and list it in OUTCOMES.
Its model, its outcome piece ("<key>_outcome") and its null constructors then exist
in .stat files; no compiler change.
"""

from statclaim.methods.core import NullForm, Outcome

CONTINUOUS = Outcome(
    key="continuous",
    module="models.two_arm_continuous",
    constructor="two_arm_continuous",
    summary="Two arms with a continuous outcome; equal-means and mean-difference nulls.",
    documentation="Two arms with a continuous outcome, such as a change in blood pressure.",
    nulls=(
        NullForm(
            "equal_means",
            "mean_treatment = mean_control",
            "Null: the two arm means are equal.",
        ),
        NullForm(
            "mean_difference_at_most",
            "mean_treatment - mean_control <= {value}",
            "Null: mean_treatment - mean_control <= value, in the outcome's units. Zero asks "
            "whether the treatment is better; a negative value is a non-inferiority margin. "
            "This direction suits an outcome where higher is better.",
            takes_value=True,
            favours="higher",
        ),
        NullForm(
            "mean_difference_at_least",
            "mean_treatment - mean_control >= {value}",
            "Null: mean_treatment - mean_control >= value, for an outcome where lower is "
            "better. Zero asks whether the treatment is better (lower); a positive value is a "
            "non-inferiority margin.",
            takes_value=True,
            favours="lower",
        ),
    ),
)

SURVIVAL = Outcome(
    key="survival",
    module="models.two_arm_survival",
    constructor="two_arm_survival",
    summary="Two arms with a time-to-event outcome, possibly censored; equal-survival null.",
    documentation="Two arms followed for the time until an event, such as death or relapse. "
    "Some participants may be censored: followed without the event being seen.",
    nulls=(
        NullForm(
            "equal_survival",
            "survival_treatment = survival_control at every time",
            "Null: the two arms have the same distribution of time to the event.",
        ),
    ),
)

# The binary outcome's model and nulls are defined by the Lean-backed module
# models.two_arm_binomial. This entry lets cited tests refer to them.
BINARY = Outcome(
    key="binary",
    module="models.two_arm_binomial",
    constructor="two_arm_binomial",
    summary="Two arms with a yes-or-no outcome.",
    documentation="Two arms with a yes-or-no outcome, such as response.",
    nulls=(
        NullForm("equal_proportions", "p_treatment = p_control", "Null: equal proportions."),
        NullForm(
            "proportion_difference",
            "p_treatment - p_control = {value}",
            "Null: the difference in proportions equals value.",
            takes_value=True,
        ),
        NullForm(
            "proportion_difference_at_most",
            "p_treatment - p_control <= {value}",
            "Null: the difference in proportions is at most value.",
            takes_value=True,
            favours="higher",
        ),
    ),
    builtin=True,
)

OUTCOMES = (CONTINUOUS, SURVIVAL, BINARY)
