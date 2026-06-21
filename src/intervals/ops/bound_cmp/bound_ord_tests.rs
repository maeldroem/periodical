use std::cmp::Ordering;
use std::fmt::Debug;

use crate::intervals::absolute::{AbsEndBound, AbsFiniteEndBound, AbsFiniteStartBound, AbsStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::ops::{BoundOrd, BoundOrdering, BoundOverlapAmbiguity, BoundOverlapDisambiguationRuleSet};
use crate::intervals::relative::{RelEndBound, RelFiniteEndBound, RelFiniteStartBound, RelStartBound};
use crate::test_data::bound_overlap::{
    FINITE_END_FINITE_END_ABS,
    FINITE_END_FINITE_END_REL,
    FINITE_END_FINITE_START_ABS,
    FINITE_END_FINITE_START_REL,
    FINITE_END_INF_END_ABS,
    FINITE_END_INF_END_REL,
    FINITE_END_INF_START_ABS,
    FINITE_END_INF_START_REL,
    FINITE_START_FINITE_END_ABS,
    FINITE_START_FINITE_END_REL,
    FINITE_START_FINITE_START_ABS,
    FINITE_START_FINITE_START_REL,
    FINITE_START_INF_END_ABS,
    FINITE_START_INF_END_REL,
    FINITE_START_INF_START_ABS,
    FINITE_START_INF_START_REL,
    INF_END_FINITE_END_ABS,
    INF_END_FINITE_END_REL,
    INF_END_FINITE_START_ABS,
    INF_END_FINITE_START_REL,
    INF_END_INF_END_ABS,
    INF_END_INF_END_REL,
    INF_END_INF_START_ABS,
    INF_END_INF_START_REL,
    INF_START_FINITE_END_ABS,
    INF_START_FINITE_END_REL,
    INF_START_FINITE_START_ABS,
    INF_START_FINITE_START_REL,
    INF_START_INF_END_ABS,
    INF_START_INF_END_REL,
    INF_START_INF_START_ABS,
    INF_START_INF_START_REL,
};
use crate::test_utils::BinOpPair;

type BodRuleSet = BoundOverlapDisambiguationRuleSet;

mod utils {
    use super::*;

    const RULE_SETS: [BodRuleSet; 5] = [
        BodRuleSet::Strict,
        BodRuleSet::Lenient,
        BodRuleSet::VeryLenient,
        BodRuleSet::ContinuousToFuture,
        BodRuleSet::ContinuousToPast,
    ];

    #[track_caller]
    pub fn assert_cmp<Lhs, Rhs, F>(lhs: &Lhs, rhs: &Rhs, expected_cmp_f: &mut F)
    where
        Lhs: BoundOrd<Rhs> + Debug,
        Rhs: Debug,
        F: FnMut(BodRuleSet) -> Ordering,
    {
        for rule_set in RULE_SETS {
            let expected_ordering = expected_cmp_f(rule_set);

            assert_eq!(
                lhs.bound_lt(rhs, rule_set),
                expected_ordering.is_lt(),
                "Is {lhs:#?} less than {rhs:#?} in rule set {rule_set:?} ?",
            );
            assert_eq!(
                lhs.bound_le(rhs, rule_set),
                expected_ordering.is_le(),
                "Is {lhs:#?} less than or equal to {rhs:#?} in rule set {rule_set:?} ?",
            );
            assert_eq!(
                lhs.bound_gt(rhs, rule_set),
                expected_ordering.is_gt(),
                "Is {lhs:#?} greater than {rhs:#?} in rule set {rule_set:?} ?",
            );
            assert_eq!(
                lhs.bound_ge(rhs, rule_set),
                expected_ordering.is_ge(),
                "Is {lhs:#?} greater than or equal to {rhs:#?} in rule set {rule_set:?} ?",
            );
        }
    }

    pub mod abs {
        use super::*;

        pub mod start_start {
            use super::*;

            pub mod fin_fin {
                use super::*;

                #[allow(clippy::too_many_lines)]
                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<AbsFiniteStartBound, AbsFiniteStartBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_start_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_finite_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_start_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_start_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_finite_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_start_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_bound(),
                        &mut expected_cmp_f,
                    );

                    assert_eq!(
                        data.lhs().to_start_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_start_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_start_bound().bound_cmp(&data.rhs().to_start_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_start_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_start_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_start_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_start_bound(),
                        &data.rhs().to_start_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_start_bound(),
                        &data.rhs().to_bound(),
                        &mut expected_cmp_f,
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_start_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_bound(),
                        &data.rhs().to_start_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }

            pub mod fin_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<AbsFiniteStartBound, AbsStartBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_finite_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_bound(),
                        &mut expected_cmp_f,
                    );

                    assert_eq!(
                        data.lhs().to_start_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_start_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_start_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_start_bound(),
                        &data.rhs().to_bound(),
                        &mut expected_cmp_f,
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }

            pub mod inf_fin {
                use super::*;

                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<AbsStartBound, AbsFiniteStartBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_start_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_finite_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_start_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_start_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_bound(),
                        &data.rhs().to_start_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }

            pub mod inf_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<AbsStartBound, AbsStartBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }
        }

        pub mod start_end {
            use super::*;

            pub mod fin_fin {
                use super::*;

                #[allow(clippy::too_many_lines)]
                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<AbsFiniteStartBound, AbsFiniteEndBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_end_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_finite_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_end_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_end_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_finite_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_end_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_bound(),
                        &mut expected_cmp_f,
                    );

                    assert_eq!(
                        data.lhs().to_start_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_start_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_start_bound().bound_cmp(&data.rhs().to_end_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_start_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_start_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_start_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_start_bound(),
                        &data.rhs().to_end_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_start_bound(),
                        &data.rhs().to_bound(),
                        &mut expected_cmp_f,
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_end_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_end_bound(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }

            pub mod fin_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<AbsFiniteStartBound, AbsEndBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_finite_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_bound(),
                        &mut expected_cmp_f,
                    );

                    assert_eq!(
                        data.lhs().to_start_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_start_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_start_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_start_bound(),
                        &data.rhs().to_bound(),
                        &mut expected_cmp_f,
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }

            pub mod inf_fin {
                use super::*;

                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<AbsStartBound, AbsFiniteEndBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_end_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_finite_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_end_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_end_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_end_bound(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }

            pub mod inf_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<AbsStartBound, AbsEndBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }
        }

        pub mod end_start {
            use super::*;

            pub mod fin_fin {
                use super::*;

                #[allow(clippy::too_many_lines)]
                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<AbsFiniteEndBound, AbsFiniteStartBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_start_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_finite_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_start_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_start_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_finite_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_start_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_bound(),
                        &mut expected_cmp_f,
                    );

                    assert_eq!(
                        data.lhs().to_end_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_cmp(&data.rhs().to_start_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_end_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_end_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_end_bound(),
                        &data.rhs().to_start_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(&data.lhs().to_end_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_start_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_bound(),
                        &data.rhs().to_start_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }

            pub mod fin_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<AbsFiniteEndBound, AbsStartBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_finite_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_bound(),
                        &mut expected_cmp_f,
                    );

                    assert_eq!(
                        data.lhs().to_end_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_end_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_end_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }

            pub mod inf_fin {
                use super::*;

                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<AbsEndBound, AbsFiniteStartBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_start_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_finite_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_start_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_start_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_bound(),
                        &data.rhs().to_start_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }

            pub mod inf_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<AbsEndBound, AbsStartBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }
        }

        pub mod end_end {
            use super::*;

            pub mod fin_fin {
                use super::*;

                #[allow(clippy::too_many_lines)]
                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<AbsFiniteEndBound, AbsFiniteEndBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_end_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_finite_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_end_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_end_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_finite_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_end_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_bound(),
                        &mut expected_cmp_f,
                    );

                    assert_eq!(
                        data.lhs().to_end_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_cmp(&data.rhs().to_end_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_end_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_end_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_end_bound(),
                        &data.rhs().to_end_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(&data.lhs().to_end_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_end_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_end_bound(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }

            pub mod fin_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<AbsFiniteEndBound, AbsEndBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_finite_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_bound(),
                        &mut expected_cmp_f,
                    );

                    assert_eq!(
                        data.lhs().to_end_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_end_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_end_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }

            pub mod inf_fin {
                use super::*;

                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<AbsEndBound, AbsFiniteEndBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_end_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_finite_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_end_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_end_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_end_bound(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }

            pub mod inf_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<AbsEndBound, AbsEndBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }
        }
    }

    pub mod rel {
        use super::*;

        pub mod start_start {
            use super::*;

            pub mod fin_fin {
                use super::*;

                #[allow(clippy::too_many_lines)]
                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<RelFiniteStartBound, RelFiniteStartBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_start_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_finite_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_start_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_start_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_finite_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_start_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_bound(),
                        &mut expected_cmp_f,
                    );

                    assert_eq!(
                        data.lhs().to_start_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_start_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_start_bound().bound_cmp(&data.rhs().to_start_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_start_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_start_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_start_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_start_bound(),
                        &data.rhs().to_start_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_start_bound(),
                        &data.rhs().to_bound(),
                        &mut expected_cmp_f,
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_start_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_bound(),
                        &data.rhs().to_start_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }

            pub mod fin_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<RelFiniteStartBound, RelStartBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_finite_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_bound(),
                        &mut expected_cmp_f,
                    );

                    assert_eq!(
                        data.lhs().to_start_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_start_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_start_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_start_bound(),
                        &data.rhs().to_bound(),
                        &mut expected_cmp_f,
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }

            pub mod inf_fin {
                use super::*;

                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<RelStartBound, RelFiniteStartBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_start_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_finite_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_start_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_start_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_bound(),
                        &data.rhs().to_start_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }

            pub mod inf_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<RelStartBound, RelStartBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }
        }

        pub mod start_end {
            use super::*;

            pub mod fin_fin {
                use super::*;

                #[allow(clippy::too_many_lines)]
                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<RelFiniteStartBound, RelFiniteEndBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_end_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_finite_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_end_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_end_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_finite_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_end_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_bound(),
                        &mut expected_cmp_f,
                    );

                    assert_eq!(
                        data.lhs().to_start_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_start_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_start_bound().bound_cmp(&data.rhs().to_end_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_start_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_start_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_start_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_start_bound(),
                        &data.rhs().to_end_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_start_bound(),
                        &data.rhs().to_bound(),
                        &mut expected_cmp_f,
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_end_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_end_bound(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }

            pub mod fin_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<RelFiniteStartBound, RelEndBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_finite_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_bound(),
                        &mut expected_cmp_f,
                    );

                    assert_eq!(
                        data.lhs().to_start_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_start_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_start_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_start_bound(),
                        &data.rhs().to_bound(),
                        &mut expected_cmp_f,
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }

            pub mod inf_fin {
                use super::*;

                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<RelStartBound, RelFiniteEndBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_end_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_finite_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_end_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_end_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_end_bound(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }

            pub mod inf_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<RelStartBound, RelEndBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }
        }

        pub mod end_start {
            use super::*;

            pub mod fin_fin {
                use super::*;

                #[allow(clippy::too_many_lines)]
                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<RelFiniteEndBound, RelFiniteStartBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_start_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_finite_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_start_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_start_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_finite_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_start_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_bound(),
                        &mut expected_cmp_f,
                    );

                    assert_eq!(
                        data.lhs().to_end_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_cmp(&data.rhs().to_start_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_end_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_end_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_end_bound(),
                        &data.rhs().to_start_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(&data.lhs().to_end_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_start_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_bound(),
                        &data.rhs().to_start_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }

            pub mod fin_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<RelFiniteEndBound, RelStartBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_finite_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_bound(),
                        &mut expected_cmp_f,
                    );

                    assert_eq!(
                        data.lhs().to_end_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_end_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_end_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }

            pub mod inf_fin {
                use super::*;

                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<RelEndBound, RelFiniteStartBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_start_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_finite_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_start_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_start_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_bound(),
                        &data.rhs().to_start_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }

            pub mod inf_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<RelEndBound, RelStartBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }
        }

        pub mod end_end {
            use super::*;

            pub mod fin_fin {
                use super::*;

                #[allow(clippy::too_many_lines)]
                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<RelFiniteEndBound, RelFiniteEndBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_end_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_finite_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_end_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_end_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_finite_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_end_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_bound(),
                        &mut expected_cmp_f,
                    );

                    assert_eq!(
                        data.lhs().to_end_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_cmp(&data.rhs().to_end_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_end_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_end_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(
                        &data.lhs().to_end_bound(),
                        &data.rhs().to_end_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(&data.lhs().to_end_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_end_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_end_bound(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }

            pub mod fin_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<RelFiniteEndBound, RelEndBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_finite_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_finite_bound(),
                        &data.rhs().to_bound(),
                        &mut expected_cmp_f,
                    );

                    assert_eq!(
                        data.lhs().to_end_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_end_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_end_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }

            pub mod inf_fin {
                use super::*;

                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<RelEndBound, RelFiniteEndBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_end_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_finite_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_end_bound(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_finite_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_end_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(
                        &data.lhs().to_bound(),
                        &data.rhs().to_finite_bound(),
                        &mut expected_cmp_f,
                    );
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_end_bound(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }

            pub mod inf_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(
                    data: &BinOpPair<RelEndBound, RelEndBound>,
                    expected_bound_ord: BoundOrdering,
                    mut expected_cmp_f: F,
                ) where
                    F: FnMut(BodRuleSet) -> Ordering,
                {
                    assert_eq!(
                        data.lhs().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(data.lhs(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(data.lhs(), &data.rhs().to_bound(), &mut expected_cmp_f);

                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(data.rhs()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_cmp(&data.rhs().to_bound()),
                        expected_bound_ord,
                        "Comparison between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                    assert_cmp(&data.lhs().to_bound(), data.rhs(), &mut expected_cmp_f);
                    assert_cmp(&data.lhs().to_bound(), &data.rhs().to_bound(), &mut expected_cmp_f);
                }
            }
        }
    }
}

mod absolute {
    use super::*;

    mod start_start {
        use super::*;

        mod finite_finite {
            use super::*;

            #[test]
            fn before() {
                utils::abs::start_start::fin_fin::assert(
                    FINITE_START_FINITE_START_ABS.get("before").unwrap(),
                    BoundOrdering::Less,
                    |_| Ordering::Less,
                );
            }

            mod equal {
                use super::*;

                #[test]
                fn inclusive_inclusive() {
                    utils::abs::start_start::fin_fin::assert(
                        FINITE_START_FINITE_START_ABS.get("equal_incl_incl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
                            BoundInclusivity::Inclusive,
                            BoundInclusivity::Inclusive,
                        ))),
                        |_| Ordering::Equal,
                    );
                }

                #[test]
                fn inclusive_exclusive() {
                    utils::abs::start_start::fin_fin::assert(
                        FINITE_START_FINITE_START_ABS.get("equal_incl_excl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
                            BoundInclusivity::Inclusive,
                            BoundInclusivity::Exclusive,
                        ))),
                        |rule_set| match rule_set {
                            BodRuleSet::Strict | BodRuleSet::ContinuousToFuture | BodRuleSet::ContinuousToPast => {
                                Ordering::Less
                            },
                            BodRuleSet::Lenient | BodRuleSet::VeryLenient => Ordering::Equal,
                        },
                    );
                }

                #[test]
                fn exclusive_inclusive() {
                    utils::abs::start_start::fin_fin::assert(
                        FINITE_START_FINITE_START_ABS.get("equal_excl_incl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
                            BoundInclusivity::Exclusive,
                            BoundInclusivity::Inclusive,
                        ))),
                        |rule_set| match rule_set {
                            BodRuleSet::Strict | BodRuleSet::ContinuousToFuture | BodRuleSet::ContinuousToPast => {
                                Ordering::Greater
                            },
                            BodRuleSet::Lenient | BodRuleSet::VeryLenient => Ordering::Equal,
                        },
                    );
                }

                #[test]
                fn exclusive_exclusive() {
                    utils::abs::start_start::fin_fin::assert(
                        FINITE_START_FINITE_START_ABS.get("equal_excl_excl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
                            BoundInclusivity::Exclusive,
                            BoundInclusivity::Exclusive,
                        ))),
                        |_| Ordering::Equal,
                    );
                }
            }

            #[test]
            fn after() {
                utils::abs::start_start::fin_fin::assert(
                    FINITE_START_FINITE_START_ABS.get("after").unwrap(),
                    BoundOrdering::Greater,
                    |_| Ordering::Greater,
                );
            }
        }

        #[test]
        fn finite_infinite() {
            utils::abs::start_start::fin_inf::assert(&FINITE_START_INF_START_ABS, BoundOrdering::Greater, |_| {
                Ordering::Greater
            });
        }

        #[test]
        fn infinite_finite() {
            utils::abs::start_start::inf_fin::assert(&INF_START_FINITE_START_ABS, BoundOrdering::Less, |_| {
                Ordering::Less
            });
        }

        #[test]
        fn infinite_infinite() {
            utils::abs::start_start::inf_inf::assert(&INF_START_INF_START_ABS, BoundOrdering::Equal(None), |_| {
                Ordering::Equal
            });
        }
    }

    mod start_end {
        use super::*;

        mod finite_finite {
            use super::*;

            #[test]
            fn before() {
                utils::abs::start_end::fin_fin::assert(
                    FINITE_START_FINITE_END_ABS.get("before").unwrap(),
                    BoundOrdering::Less,
                    |_| Ordering::Less,
                );
            }

            mod equal {
                use super::*;

                #[test]
                fn inclusive_inclusive() {
                    utils::abs::start_end::fin_fin::assert(
                        FINITE_START_FINITE_END_ABS.get("equal_incl_incl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
                            BoundInclusivity::Inclusive,
                            BoundInclusivity::Inclusive,
                        ))),
                        |_| Ordering::Equal,
                    );
                }

                #[test]
                fn inclusive_exclusive() {
                    utils::abs::start_end::fin_fin::assert(
                        FINITE_START_FINITE_END_ABS.get("equal_incl_excl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
                            BoundInclusivity::Inclusive,
                            BoundInclusivity::Exclusive,
                        ))),
                        |rule_set| match rule_set {
                            BodRuleSet::Strict | BodRuleSet::ContinuousToPast => Ordering::Greater,
                            BodRuleSet::Lenient | BodRuleSet::VeryLenient | BodRuleSet::ContinuousToFuture => {
                                Ordering::Equal
                            },
                        },
                    );
                }

                #[test]
                fn exclusive_inclusive() {
                    utils::abs::start_end::fin_fin::assert(
                        FINITE_START_FINITE_END_ABS.get("equal_excl_incl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
                            BoundInclusivity::Exclusive,
                            BoundInclusivity::Inclusive,
                        ))),
                        |rule_set| match rule_set {
                            BodRuleSet::Strict | BodRuleSet::ContinuousToFuture => Ordering::Greater,
                            BodRuleSet::Lenient | BodRuleSet::VeryLenient | BodRuleSet::ContinuousToPast => {
                                Ordering::Equal
                            },
                        },
                    );
                }

                #[test]
                fn exclusive_exclusive() {
                    utils::abs::start_end::fin_fin::assert(
                        FINITE_START_FINITE_END_ABS.get("equal_excl_excl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
                            BoundInclusivity::Exclusive,
                            BoundInclusivity::Exclusive,
                        ))),
                        |rule_set| match rule_set {
                            BodRuleSet::Strict
                            | BodRuleSet::Lenient
                            | BodRuleSet::ContinuousToFuture
                            | BodRuleSet::ContinuousToPast => Ordering::Greater,
                            BodRuleSet::VeryLenient => Ordering::Equal,
                        },
                    );
                }
            }

            #[test]
            fn after() {
                utils::abs::start_end::fin_fin::assert(
                    FINITE_START_FINITE_END_ABS.get("after").unwrap(),
                    BoundOrdering::Greater,
                    |_| Ordering::Greater,
                );
            }
        }

        #[test]
        fn finite_infinite() {
            utils::abs::start_end::fin_inf::assert(&FINITE_START_INF_END_ABS, BoundOrdering::Less, |_| Ordering::Less);
        }

        #[test]
        fn infinite_finite() {
            utils::abs::start_end::inf_fin::assert(&INF_START_FINITE_END_ABS, BoundOrdering::Less, |_| Ordering::Less);
        }

        #[test]
        fn infinite_infinite() {
            utils::abs::start_end::inf_inf::assert(&INF_START_INF_END_ABS, BoundOrdering::Less, |_| Ordering::Less);
        }
    }

    mod end_start {
        use super::*;

        mod finite_finite {
            use super::*;

            #[test]
            fn before() {
                utils::abs::end_start::fin_fin::assert(
                    FINITE_END_FINITE_START_ABS.get("before").unwrap(),
                    BoundOrdering::Less,
                    |_| Ordering::Less,
                );
            }

            mod equal {
                use super::*;

                #[test]
                fn inclusive_inclusive() {
                    utils::abs::end_start::fin_fin::assert(
                        FINITE_END_FINITE_START_ABS.get("equal_incl_incl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
                            BoundInclusivity::Inclusive,
                            BoundInclusivity::Inclusive,
                        ))),
                        |_| Ordering::Equal,
                    );
                }

                #[test]
                fn inclusive_exclusive() {
                    utils::abs::end_start::fin_fin::assert(
                        FINITE_END_FINITE_START_ABS.get("equal_incl_excl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
                            BoundInclusivity::Inclusive,
                            BoundInclusivity::Exclusive,
                        ))),
                        |rule_set| match rule_set {
                            BodRuleSet::Strict | BodRuleSet::ContinuousToFuture => Ordering::Less,
                            BodRuleSet::Lenient | BodRuleSet::VeryLenient | BodRuleSet::ContinuousToPast => {
                                Ordering::Equal
                            },
                        },
                    );
                }

                #[test]
                fn exclusive_inclusive() {
                    utils::abs::end_start::fin_fin::assert(
                        FINITE_END_FINITE_START_ABS.get("equal_excl_incl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
                            BoundInclusivity::Exclusive,
                            BoundInclusivity::Inclusive,
                        ))),
                        |rule_set| match rule_set {
                            BodRuleSet::Strict | BodRuleSet::ContinuousToPast => Ordering::Less,
                            BodRuleSet::Lenient | BodRuleSet::VeryLenient | BodRuleSet::ContinuousToFuture => {
                                Ordering::Equal
                            },
                        },
                    );
                }

                #[test]
                fn exclusive_exclusive() {
                    utils::abs::end_start::fin_fin::assert(
                        FINITE_END_FINITE_START_ABS.get("equal_excl_excl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
                            BoundInclusivity::Exclusive,
                            BoundInclusivity::Exclusive,
                        ))),
                        |rule_set| match rule_set {
                            BodRuleSet::Strict
                            | BodRuleSet::Lenient
                            | BodRuleSet::ContinuousToFuture
                            | BodRuleSet::ContinuousToPast => Ordering::Less,
                            BodRuleSet::VeryLenient => Ordering::Equal,
                        },
                    );
                }
            }

            #[test]
            fn after() {
                utils::abs::end_start::fin_fin::assert(
                    FINITE_END_FINITE_START_ABS.get("after").unwrap(),
                    BoundOrdering::Greater,
                    |_| Ordering::Greater,
                );
            }
        }

        #[test]
        fn finite_infinite() {
            utils::abs::end_start::fin_inf::assert(&FINITE_END_INF_START_ABS, BoundOrdering::Greater, |_| {
                Ordering::Greater
            });
        }

        #[test]
        fn infinite_finite() {
            utils::abs::end_start::inf_fin::assert(&INF_END_FINITE_START_ABS, BoundOrdering::Greater, |_| {
                Ordering::Greater
            });
        }

        #[test]
        fn infinite_infinite() {
            utils::abs::end_start::inf_inf::assert(&INF_END_INF_START_ABS, BoundOrdering::Greater, |_| {
                Ordering::Greater
            });
        }
    }

    mod end_end {
        use super::*;

        mod finite_finite {
            use super::*;

            #[test]
            fn before() {
                utils::abs::end_end::fin_fin::assert(
                    FINITE_END_FINITE_END_ABS.get("before").unwrap(),
                    BoundOrdering::Less,
                    |_| Ordering::Less,
                );
            }

            mod equal {
                use super::*;

                #[test]
                fn inclusive_inclusive() {
                    utils::abs::end_end::fin_fin::assert(
                        FINITE_END_FINITE_END_ABS.get("equal_incl_incl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
                            BoundInclusivity::Inclusive,
                            BoundInclusivity::Inclusive,
                        ))),
                        |_| Ordering::Equal,
                    );
                }

                #[test]
                fn inclusive_exclusive() {
                    utils::abs::end_end::fin_fin::assert(
                        FINITE_END_FINITE_END_ABS.get("equal_incl_excl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
                            BoundInclusivity::Inclusive,
                            BoundInclusivity::Exclusive,
                        ))),
                        |rule_set| match rule_set {
                            BodRuleSet::Strict | BodRuleSet::ContinuousToFuture | BodRuleSet::ContinuousToPast => {
                                Ordering::Greater
                            },
                            BodRuleSet::Lenient | BodRuleSet::VeryLenient => Ordering::Equal,
                        },
                    );
                }

                #[test]
                fn exclusive_inclusive() {
                    utils::abs::end_end::fin_fin::assert(
                        FINITE_END_FINITE_END_ABS.get("equal_excl_incl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
                            BoundInclusivity::Exclusive,
                            BoundInclusivity::Inclusive,
                        ))),
                        |rule_set| match rule_set {
                            BodRuleSet::Strict | BodRuleSet::ContinuousToFuture | BodRuleSet::ContinuousToPast => {
                                Ordering::Less
                            },
                            BodRuleSet::Lenient | BodRuleSet::VeryLenient => Ordering::Equal,
                        },
                    );
                }

                #[test]
                fn exclusive_exclusive() {
                    utils::abs::end_end::fin_fin::assert(
                        FINITE_END_FINITE_END_ABS.get("equal_excl_excl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
                            BoundInclusivity::Exclusive,
                            BoundInclusivity::Exclusive,
                        ))),
                        |_| Ordering::Equal,
                    );
                }
            }

            #[test]
            fn after() {
                utils::abs::end_end::fin_fin::assert(
                    FINITE_END_FINITE_END_ABS.get("after").unwrap(),
                    BoundOrdering::Greater,
                    |_| Ordering::Greater,
                );
            }
        }

        #[test]
        fn finite_infinite() {
            utils::abs::end_end::fin_inf::assert(&FINITE_END_INF_END_ABS, BoundOrdering::Less, |_| Ordering::Less);
        }

        #[test]
        fn infinite_finite() {
            utils::abs::end_end::inf_fin::assert(&INF_END_FINITE_END_ABS, BoundOrdering::Greater, |_| {
                Ordering::Greater
            });
        }

        #[test]
        fn infinite_infinite() {
            utils::abs::end_end::inf_inf::assert(&INF_END_INF_END_ABS, BoundOrdering::Equal(None), |_| Ordering::Equal);
        }
    }
}

mod relative {
    use super::*;

    mod start_start {
        use super::*;

        mod finite_finite {
            use super::*;

            #[test]
            fn before() {
                utils::rel::start_start::fin_fin::assert(
                    FINITE_START_FINITE_START_REL.get("before").unwrap(),
                    BoundOrdering::Less,
                    |_| Ordering::Less,
                );
            }

            mod equal {
                use super::*;

                #[test]
                fn inclusive_inclusive() {
                    utils::rel::start_start::fin_fin::assert(
                        FINITE_START_FINITE_START_REL.get("equal_incl_incl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
                            BoundInclusivity::Inclusive,
                            BoundInclusivity::Inclusive,
                        ))),
                        |_| Ordering::Equal,
                    );
                }

                #[test]
                fn inclusive_exclusive() {
                    utils::rel::start_start::fin_fin::assert(
                        FINITE_START_FINITE_START_REL.get("equal_incl_excl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
                            BoundInclusivity::Inclusive,
                            BoundInclusivity::Exclusive,
                        ))),
                        |rule_set| match rule_set {
                            BodRuleSet::Strict | BodRuleSet::ContinuousToFuture | BodRuleSet::ContinuousToPast => {
                                Ordering::Less
                            },
                            BodRuleSet::Lenient | BodRuleSet::VeryLenient => Ordering::Equal,
                        },
                    );
                }

                #[test]
                fn exclusive_inclusive() {
                    utils::rel::start_start::fin_fin::assert(
                        FINITE_START_FINITE_START_REL.get("equal_excl_incl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
                            BoundInclusivity::Exclusive,
                            BoundInclusivity::Inclusive,
                        ))),
                        |rule_set| match rule_set {
                            BodRuleSet::Strict | BodRuleSet::ContinuousToFuture | BodRuleSet::ContinuousToPast => {
                                Ordering::Greater
                            },
                            BodRuleSet::Lenient | BodRuleSet::VeryLenient => Ordering::Equal,
                        },
                    );
                }

                #[test]
                fn exclusive_exclusive() {
                    utils::rel::start_start::fin_fin::assert(
                        FINITE_START_FINITE_START_REL.get("equal_excl_excl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
                            BoundInclusivity::Exclusive,
                            BoundInclusivity::Exclusive,
                        ))),
                        |_| Ordering::Equal,
                    );
                }
            }

            #[test]
            fn after() {
                utils::rel::start_start::fin_fin::assert(
                    FINITE_START_FINITE_START_REL.get("after").unwrap(),
                    BoundOrdering::Greater,
                    |_| Ordering::Greater,
                );
            }
        }

        #[test]
        fn finite_infinite() {
            utils::rel::start_start::fin_inf::assert(&FINITE_START_INF_START_REL, BoundOrdering::Greater, |_| {
                Ordering::Greater
            });
        }

        #[test]
        fn infinite_finite() {
            utils::rel::start_start::inf_fin::assert(&INF_START_FINITE_START_REL, BoundOrdering::Less, |_| {
                Ordering::Less
            });
        }

        #[test]
        fn infinite_infinite() {
            utils::rel::start_start::inf_inf::assert(&INF_START_INF_START_REL, BoundOrdering::Equal(None), |_| {
                Ordering::Equal
            });
        }
    }

    mod start_end {
        use super::*;

        mod finite_finite {
            use super::*;

            #[test]
            fn before() {
                utils::rel::start_end::fin_fin::assert(
                    FINITE_START_FINITE_END_REL.get("before").unwrap(),
                    BoundOrdering::Less,
                    |_| Ordering::Less,
                );
            }

            mod equal {
                use super::*;

                #[test]
                fn inclusive_inclusive() {
                    utils::rel::start_end::fin_fin::assert(
                        FINITE_START_FINITE_END_REL.get("equal_incl_incl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
                            BoundInclusivity::Inclusive,
                            BoundInclusivity::Inclusive,
                        ))),
                        |_| Ordering::Equal,
                    );
                }

                #[test]
                fn inclusive_exclusive() {
                    utils::rel::start_end::fin_fin::assert(
                        FINITE_START_FINITE_END_REL.get("equal_incl_excl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
                            BoundInclusivity::Inclusive,
                            BoundInclusivity::Exclusive,
                        ))),
                        |rule_set| match rule_set {
                            BodRuleSet::Strict | BodRuleSet::ContinuousToPast => Ordering::Greater,
                            BodRuleSet::Lenient | BodRuleSet::VeryLenient | BodRuleSet::ContinuousToFuture => {
                                Ordering::Equal
                            },
                        },
                    );
                }

                #[test]
                fn exclusive_inclusive() {
                    utils::rel::start_end::fin_fin::assert(
                        FINITE_START_FINITE_END_REL.get("equal_excl_incl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
                            BoundInclusivity::Exclusive,
                            BoundInclusivity::Inclusive,
                        ))),
                        |rule_set| match rule_set {
                            BodRuleSet::Strict | BodRuleSet::ContinuousToFuture => Ordering::Greater,
                            BodRuleSet::Lenient | BodRuleSet::VeryLenient | BodRuleSet::ContinuousToPast => {
                                Ordering::Equal
                            },
                        },
                    );
                }

                #[test]
                fn exclusive_exclusive() {
                    utils::rel::start_end::fin_fin::assert(
                        FINITE_START_FINITE_END_REL.get("equal_excl_excl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
                            BoundInclusivity::Exclusive,
                            BoundInclusivity::Exclusive,
                        ))),
                        |rule_set| match rule_set {
                            BodRuleSet::Strict
                            | BodRuleSet::Lenient
                            | BodRuleSet::ContinuousToFuture
                            | BodRuleSet::ContinuousToPast => Ordering::Greater,
                            BodRuleSet::VeryLenient => Ordering::Equal,
                        },
                    );
                }
            }

            #[test]
            fn after() {
                utils::rel::start_end::fin_fin::assert(
                    FINITE_START_FINITE_END_REL.get("after").unwrap(),
                    BoundOrdering::Greater,
                    |_| Ordering::Greater,
                );
            }
        }

        #[test]
        fn finite_infinite() {
            utils::rel::start_end::fin_inf::assert(&FINITE_START_INF_END_REL, BoundOrdering::Less, |_| Ordering::Less);
        }

        #[test]
        fn infinite_finite() {
            utils::rel::start_end::inf_fin::assert(&INF_START_FINITE_END_REL, BoundOrdering::Less, |_| Ordering::Less);
        }

        #[test]
        fn infinite_infinite() {
            utils::rel::start_end::inf_inf::assert(&INF_START_INF_END_REL, BoundOrdering::Less, |_| Ordering::Less);
        }
    }

    mod end_start {
        use super::*;

        mod finite_finite {
            use super::*;

            #[test]
            fn before() {
                utils::rel::end_start::fin_fin::assert(
                    FINITE_END_FINITE_START_REL.get("before").unwrap(),
                    BoundOrdering::Less,
                    |_| Ordering::Less,
                );
            }

            mod equal {
                use super::*;

                #[test]
                fn inclusive_inclusive() {
                    utils::rel::end_start::fin_fin::assert(
                        FINITE_END_FINITE_START_REL.get("equal_incl_incl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
                            BoundInclusivity::Inclusive,
                            BoundInclusivity::Inclusive,
                        ))),
                        |_| Ordering::Equal,
                    );
                }

                #[test]
                fn inclusive_exclusive() {
                    utils::rel::end_start::fin_fin::assert(
                        FINITE_END_FINITE_START_REL.get("equal_incl_excl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
                            BoundInclusivity::Inclusive,
                            BoundInclusivity::Exclusive,
                        ))),
                        |rule_set| match rule_set {
                            BodRuleSet::Strict | BodRuleSet::ContinuousToFuture => Ordering::Less,
                            BodRuleSet::Lenient | BodRuleSet::VeryLenient | BodRuleSet::ContinuousToPast => {
                                Ordering::Equal
                            },
                        },
                    );
                }

                #[test]
                fn exclusive_inclusive() {
                    utils::rel::end_start::fin_fin::assert(
                        FINITE_END_FINITE_START_REL.get("equal_excl_incl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
                            BoundInclusivity::Exclusive,
                            BoundInclusivity::Inclusive,
                        ))),
                        |rule_set| match rule_set {
                            BodRuleSet::Strict | BodRuleSet::ContinuousToPast => Ordering::Less,
                            BodRuleSet::Lenient | BodRuleSet::VeryLenient | BodRuleSet::ContinuousToFuture => {
                                Ordering::Equal
                            },
                        },
                    );
                }

                #[test]
                fn exclusive_exclusive() {
                    utils::rel::end_start::fin_fin::assert(
                        FINITE_END_FINITE_START_REL.get("equal_excl_excl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
                            BoundInclusivity::Exclusive,
                            BoundInclusivity::Exclusive,
                        ))),
                        |rule_set| match rule_set {
                            BodRuleSet::Strict
                            | BodRuleSet::Lenient
                            | BodRuleSet::ContinuousToFuture
                            | BodRuleSet::ContinuousToPast => Ordering::Less,
                            BodRuleSet::VeryLenient => Ordering::Equal,
                        },
                    );
                }
            }

            #[test]
            fn after() {
                utils::rel::end_start::fin_fin::assert(
                    FINITE_END_FINITE_START_REL.get("after").unwrap(),
                    BoundOrdering::Greater,
                    |_| Ordering::Greater,
                );
            }
        }

        #[test]
        fn finite_infinite() {
            utils::rel::end_start::fin_inf::assert(&FINITE_END_INF_START_REL, BoundOrdering::Greater, |_| {
                Ordering::Greater
            });
        }

        #[test]
        fn infinite_finite() {
            utils::rel::end_start::inf_fin::assert(&INF_END_FINITE_START_REL, BoundOrdering::Greater, |_| {
                Ordering::Greater
            });
        }

        #[test]
        fn infinite_infinite() {
            utils::rel::end_start::inf_inf::assert(&INF_END_INF_START_REL, BoundOrdering::Greater, |_| {
                Ordering::Greater
            });
        }
    }

    mod end_end {
        use super::*;

        mod finite_finite {
            use super::*;

            #[test]
            fn before() {
                utils::rel::end_end::fin_fin::assert(
                    FINITE_END_FINITE_END_REL.get("before").unwrap(),
                    BoundOrdering::Less,
                    |_| Ordering::Less,
                );
            }

            mod equal {
                use super::*;

                #[test]
                fn inclusive_inclusive() {
                    utils::rel::end_end::fin_fin::assert(
                        FINITE_END_FINITE_END_REL.get("equal_incl_incl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
                            BoundInclusivity::Inclusive,
                            BoundInclusivity::Inclusive,
                        ))),
                        |_| Ordering::Equal,
                    );
                }

                #[test]
                fn inclusive_exclusive() {
                    utils::rel::end_end::fin_fin::assert(
                        FINITE_END_FINITE_END_REL.get("equal_incl_excl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
                            BoundInclusivity::Inclusive,
                            BoundInclusivity::Exclusive,
                        ))),
                        |rule_set| match rule_set {
                            BodRuleSet::Strict | BodRuleSet::ContinuousToFuture | BodRuleSet::ContinuousToPast => {
                                Ordering::Greater
                            },
                            BodRuleSet::Lenient | BodRuleSet::VeryLenient => Ordering::Equal,
                        },
                    );
                }

                #[test]
                fn exclusive_inclusive() {
                    utils::rel::end_end::fin_fin::assert(
                        FINITE_END_FINITE_END_REL.get("equal_excl_incl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
                            BoundInclusivity::Exclusive,
                            BoundInclusivity::Inclusive,
                        ))),
                        |rule_set| match rule_set {
                            BodRuleSet::Strict | BodRuleSet::ContinuousToFuture | BodRuleSet::ContinuousToPast => {
                                Ordering::Less
                            },
                            BodRuleSet::Lenient | BodRuleSet::VeryLenient => Ordering::Equal,
                        },
                    );
                }

                #[test]
                fn exclusive_exclusive() {
                    utils::rel::end_end::fin_fin::assert(
                        FINITE_END_FINITE_END_REL.get("equal_excl_excl").unwrap(),
                        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
                            BoundInclusivity::Exclusive,
                            BoundInclusivity::Exclusive,
                        ))),
                        |_| Ordering::Equal,
                    );
                }
            }

            #[test]
            fn after() {
                utils::rel::end_end::fin_fin::assert(
                    FINITE_END_FINITE_END_REL.get("after").unwrap(),
                    BoundOrdering::Greater,
                    |_| Ordering::Greater,
                );
            }
        }

        #[test]
        fn finite_infinite() {
            utils::rel::end_end::fin_inf::assert(&FINITE_END_INF_END_REL, BoundOrdering::Less, |_| Ordering::Less);
        }

        #[test]
        fn infinite_finite() {
            utils::rel::end_end::inf_fin::assert(&INF_END_FINITE_END_REL, BoundOrdering::Greater, |_| {
                Ordering::Greater
            });
        }

        #[test]
        fn infinite_infinite() {
            utils::rel::end_end::inf_inf::assert(&INF_END_INF_END_REL, BoundOrdering::Equal(None), |_| Ordering::Equal);
        }
    }
}
