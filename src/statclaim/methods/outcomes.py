"""Kinds of two-arm outcome and the null hypotheses that can be stated about each.

To support a new kind of endpoint, add an Outcome here and list it in OUTCOMES.
Its model and null constructors then exist in .stat files; no compiler change.
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
            "whether the treatment is better; a negative value is a non-inferiority margin.",
            takes_value=True,
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

OUTCOMES = (CONTINUOUS, SURVIVAL)
