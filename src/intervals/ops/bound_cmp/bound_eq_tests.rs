use crate::intervals::absolute::{AbsEndBound, AbsFiniteEndBound, AbsFiniteStartBound, AbsStartBound};
use crate::intervals::ops::{BoundEq, BoundOverlapDisambiguationRuleSet};
use crate::intervals::relative::{RelEndBound, RelFiniteEndBound, RelFiniteStartBound, RelStartBound};
use crate::test_data::BinOpPair;
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

type BodRuleSet = BoundOverlapDisambiguationRuleSet;

pub mod utils {
    use super::*;

    pub mod abs {
        use super::*;

        pub mod start_start {
            use super::*;

            pub mod fin_fin {
                use super::*;

                #[allow(clippy::too_many_lines)]
                pub fn assert(
                    data: &BinOpPair<AbsFiniteStartBound, AbsFiniteStartBound>,
                    rule_set: BodRuleSet,
                    expected: bool,
                ) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_start_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_finite_bound()
                            .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_finite_bound()
                            .bound_eq(&data.rhs().to_start_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_start_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_start_bound()
                            .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_start_bound()
                            .bound_eq(&data.rhs().to_start_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_start_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_start_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }

            pub mod fin_inf {
                use super::*;

                pub fn assert(
                    data: &BinOpPair<AbsFiniteStartBound, AbsStartBound>,
                    rule_set: BodRuleSet,
                    expected: bool,
                ) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_start_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_start_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }

            pub mod inf_fin {
                use super::*;

                pub fn assert(
                    data: &BinOpPair<AbsStartBound, AbsFiniteStartBound>,
                    rule_set: BodRuleSet,
                    expected: bool,
                ) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_start_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_start_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }

            pub mod inf_inf {
                use super::*;

                pub fn assert(data: &BinOpPair<AbsStartBound, AbsStartBound>, rule_set: BodRuleSet, expected: bool) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }
        }

        pub mod start_end {
            use super::*;

            pub mod fin_fin {
                use super::*;

                #[allow(clippy::too_many_lines)]
                pub fn assert(
                    data: &BinOpPair<AbsFiniteStartBound, AbsFiniteEndBound>,
                    rule_set: BodRuleSet,
                    expected: bool,
                ) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_end_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_finite_bound()
                            .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_finite_bound()
                            .bound_eq(&data.rhs().to_end_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_start_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_start_bound()
                            .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_start_bound()
                            .bound_eq(&data.rhs().to_end_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_start_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_end_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }

            pub mod fin_inf {
                use super::*;

                pub fn assert(
                    data: &BinOpPair<AbsFiniteStartBound, AbsEndBound>,
                    rule_set: BodRuleSet,
                    expected: bool,
                ) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_start_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_start_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }

            pub mod inf_fin {
                use super::*;

                pub fn assert(
                    data: &BinOpPair<AbsStartBound, AbsFiniteEndBound>,
                    rule_set: BodRuleSet,
                    expected: bool,
                ) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_end_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_end_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }

            pub mod inf_inf {
                use super::*;

                pub fn assert(data: &BinOpPair<AbsStartBound, AbsEndBound>, rule_set: BodRuleSet, expected: bool) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }
        }

        pub mod end_start {
            use super::*;

            pub mod fin_fin {
                use super::*;

                #[allow(clippy::too_many_lines)]
                pub fn assert(
                    data: &BinOpPair<AbsFiniteEndBound, AbsFiniteStartBound>,
                    rule_set: BodRuleSet,
                    expected: bool,
                ) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_start_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_finite_bound()
                            .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_finite_bound()
                            .bound_eq(&data.rhs().to_start_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_end_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_end_bound()
                            .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_end_bound()
                            .bound_eq(&data.rhs().to_start_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_start_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }

            pub mod fin_inf {
                use super::*;

                pub fn assert(
                    data: &BinOpPair<AbsFiniteEndBound, AbsStartBound>,
                    rule_set: BodRuleSet,
                    expected: bool,
                ) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_end_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }

            pub mod inf_fin {
                use super::*;

                pub fn assert(
                    data: &BinOpPair<AbsEndBound, AbsFiniteStartBound>,
                    rule_set: BodRuleSet,
                    expected: bool,
                ) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_start_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_start_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }

            pub mod inf_inf {
                use super::*;

                pub fn assert(data: &BinOpPair<AbsEndBound, AbsStartBound>, rule_set: BodRuleSet, expected: bool) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }
        }

        pub mod end_end {
            use super::*;

            pub mod fin_fin {
                use super::*;

                #[allow(clippy::too_many_lines)]
                pub fn assert(
                    data: &BinOpPair<AbsFiniteEndBound, AbsFiniteEndBound>,
                    rule_set: BodRuleSet,
                    expected: bool,
                ) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_end_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_finite_bound()
                            .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_finite_bound()
                            .bound_eq(&data.rhs().to_end_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_end_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_end_bound()
                            .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_eq(&data.rhs().to_end_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_end_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }

            pub mod fin_inf {
                use super::*;

                pub fn assert(data: &BinOpPair<AbsFiniteEndBound, AbsEndBound>, rule_set: BodRuleSet, expected: bool) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_end_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }

            pub mod inf_fin {
                use super::*;

                pub fn assert(data: &BinOpPair<AbsEndBound, AbsFiniteEndBound>, rule_set: BodRuleSet, expected: bool) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_end_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_end_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }

            pub mod inf_inf {
                use super::*;

                pub fn assert(data: &BinOpPair<AbsEndBound, AbsEndBound>, rule_set: BodRuleSet, expected: bool) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
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
                pub fn assert(
                    data: &BinOpPair<RelFiniteStartBound, RelFiniteStartBound>,
                    rule_set: BodRuleSet,
                    expected: bool,
                ) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_start_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_finite_bound()
                            .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_finite_bound()
                            .bound_eq(&data.rhs().to_start_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_start_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_start_bound()
                            .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_start_bound()
                            .bound_eq(&data.rhs().to_start_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_start_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_start_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }

            pub mod fin_inf {
                use super::*;

                pub fn assert(
                    data: &BinOpPair<RelFiniteStartBound, RelStartBound>,
                    rule_set: BodRuleSet,
                    expected: bool,
                ) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_start_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_start_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }

            pub mod inf_fin {
                use super::*;

                pub fn assert(
                    data: &BinOpPair<RelStartBound, RelFiniteStartBound>,
                    rule_set: BodRuleSet,
                    expected: bool,
                ) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_start_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_start_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }

            pub mod inf_inf {
                use super::*;

                pub fn assert(data: &BinOpPair<RelStartBound, RelStartBound>, rule_set: BodRuleSet, expected: bool) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }
        }

        pub mod start_end {
            use super::*;

            pub mod fin_fin {
                use super::*;

                #[allow(clippy::too_many_lines)]
                pub fn assert(
                    data: &BinOpPair<RelFiniteStartBound, RelFiniteEndBound>,
                    rule_set: BodRuleSet,
                    expected: bool,
                ) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_end_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_finite_bound()
                            .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_finite_bound()
                            .bound_eq(&data.rhs().to_end_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_start_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_start_bound()
                            .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_start_bound()
                            .bound_eq(&data.rhs().to_end_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_start_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_end_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }

            pub mod fin_inf {
                use super::*;

                pub fn assert(
                    data: &BinOpPair<RelFiniteStartBound, RelEndBound>,
                    rule_set: BodRuleSet,
                    expected: bool,
                ) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_start_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_start_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_start_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }

            pub mod inf_fin {
                use super::*;

                pub fn assert(
                    data: &BinOpPair<RelStartBound, RelFiniteEndBound>,
                    rule_set: BodRuleSet,
                    expected: bool,
                ) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_end_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_end_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }

            pub mod inf_inf {
                use super::*;

                pub fn assert(data: &BinOpPair<RelStartBound, RelEndBound>, rule_set: BodRuleSet, expected: bool) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }
        }

        pub mod end_start {
            use super::*;

            pub mod fin_fin {
                use super::*;

                #[allow(clippy::too_many_lines)]
                pub fn assert(
                    data: &BinOpPair<RelFiniteEndBound, RelFiniteStartBound>,
                    rule_set: BodRuleSet,
                    expected: bool,
                ) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_start_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_finite_bound()
                            .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_finite_bound()
                            .bound_eq(&data.rhs().to_start_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_end_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_end_bound()
                            .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_end_bound()
                            .bound_eq(&data.rhs().to_start_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_start_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }

            pub mod fin_inf {
                use super::*;

                pub fn assert(
                    data: &BinOpPair<RelFiniteEndBound, RelStartBound>,
                    rule_set: BodRuleSet,
                    expected: bool,
                ) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_end_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }

            pub mod inf_fin {
                use super::*;

                pub fn assert(
                    data: &BinOpPair<RelEndBound, RelFiniteStartBound>,
                    rule_set: BodRuleSet,
                    expected: bool,
                ) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_start_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_start_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_start_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }

            pub mod inf_inf {
                use super::*;

                pub fn assert(data: &BinOpPair<RelEndBound, RelStartBound>, rule_set: BodRuleSet, expected: bool) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }
        }

        pub mod end_end {
            use super::*;

            pub mod fin_fin {
                use super::*;

                #[allow(clippy::too_many_lines)]
                pub fn assert(
                    data: &BinOpPair<RelFiniteEndBound, RelFiniteEndBound>,
                    rule_set: BodRuleSet,
                    expected: bool,
                ) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_end_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_finite_bound()
                            .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_finite_bound()
                            .bound_eq(&data.rhs().to_end_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_end_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs()
                            .to_end_bound()
                            .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_eq(&data.rhs().to_end_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_end_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }

            pub mod fin_inf {
                use super::*;

                pub fn assert(data: &BinOpPair<RelFiniteEndBound, RelEndBound>, rule_set: BodRuleSet, expected: bool) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_finite_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_end_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_end_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_end_bound(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }

            pub mod inf_fin {
                use super::*;

                pub fn assert(data: &BinOpPair<RelEndBound, RelFiniteEndBound>, rule_set: BodRuleSet, expected: bool) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_end_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_finite_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_end_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_end_bound(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
                }
            }

            pub mod inf_inf {
                use super::*;

                pub fn assert(data: &BinOpPair<RelEndBound, RelEndBound>, rule_set: BodRuleSet, expected: bool) {
                    assert_eq!(
                        data.lhs().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs(),
                        data.rhs().to_bound(),
                    );

                    assert_eq!(
                        data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs(),
                    );
                    assert_eq!(
                        data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                        expected,
                        "Equality between {:#?} and {:#?}",
                        data.lhs().to_bound(),
                        data.rhs().to_bound(),
                    );
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
                let data = FINITE_START_FINITE_START_ABS.get("before").unwrap();

                utils::abs::start_start::fin_fin::assert(data, BodRuleSet::Strict, false);
                utils::abs::start_start::fin_fin::assert(data, BodRuleSet::Lenient, false);
                utils::abs::start_start::fin_fin::assert(data, BodRuleSet::VeryLenient, false);
                utils::abs::start_start::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                utils::abs::start_start::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
            }

            mod equal {
                use super::*;

                #[test]
                fn inclusive_inclusive() {
                    let data = FINITE_START_FINITE_START_ABS.get("equal_incl_incl").unwrap();

                    utils::abs::start_start::fin_fin::assert(data, BodRuleSet::Strict, true);
                    utils::abs::start_start::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::abs::start_start::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::abs::start_start::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, true);
                    utils::abs::start_start::fin_fin::assert(data, BodRuleSet::ContinuousToPast, true);
                }

                #[test]
                fn inclusive_exclusive() {
                    let data = FINITE_START_FINITE_START_ABS.get("equal_incl_excl").unwrap();

                    utils::abs::start_start::fin_fin::assert(data, BodRuleSet::Strict, false);
                    utils::abs::start_start::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::abs::start_start::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::abs::start_start::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                    utils::abs::start_start::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
                }

                #[test]
                fn exclusive_inclusive() {
                    let data = FINITE_START_FINITE_START_ABS.get("equal_excl_incl").unwrap();

                    utils::abs::start_start::fin_fin::assert(data, BodRuleSet::Strict, false);
                    utils::abs::start_start::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::abs::start_start::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::abs::start_start::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                    utils::abs::start_start::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
                }

                #[test]
                fn exclusive_exclusive() {
                    let data = FINITE_START_FINITE_START_ABS.get("equal_excl_excl").unwrap();

                    utils::abs::start_start::fin_fin::assert(data, BodRuleSet::Strict, true);
                    utils::abs::start_start::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::abs::start_start::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::abs::start_start::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, true);
                    utils::abs::start_start::fin_fin::assert(data, BodRuleSet::ContinuousToPast, true);
                }
            }

            #[test]
            fn after() {
                let data = FINITE_START_FINITE_START_ABS.get("after").unwrap();

                utils::abs::start_start::fin_fin::assert(data, BodRuleSet::Strict, false);
                utils::abs::start_start::fin_fin::assert(data, BodRuleSet::Lenient, false);
                utils::abs::start_start::fin_fin::assert(data, BodRuleSet::VeryLenient, false);
                utils::abs::start_start::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                utils::abs::start_start::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
            }
        }

        #[test]
        fn finite_infinite() {
            let data = &*FINITE_START_INF_START_ABS;

            utils::abs::start_start::fin_inf::assert(data, BodRuleSet::Strict, false);
            utils::abs::start_start::fin_inf::assert(data, BodRuleSet::Lenient, false);
            utils::abs::start_start::fin_inf::assert(data, BodRuleSet::VeryLenient, false);
            utils::abs::start_start::fin_inf::assert(data, BodRuleSet::ContinuousToFuture, false);
            utils::abs::start_start::fin_inf::assert(data, BodRuleSet::ContinuousToPast, false);
        }

        #[test]
        fn infinite_finite() {
            let data = &*INF_START_FINITE_START_ABS;

            utils::abs::start_start::inf_fin::assert(data, BodRuleSet::Strict, false);
            utils::abs::start_start::inf_fin::assert(data, BodRuleSet::Lenient, false);
            utils::abs::start_start::inf_fin::assert(data, BodRuleSet::VeryLenient, false);
            utils::abs::start_start::inf_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
            utils::abs::start_start::inf_fin::assert(data, BodRuleSet::ContinuousToPast, false);
        }

        #[test]
        fn infinite_infinite() {
            let data = &*INF_START_INF_START_ABS;

            utils::abs::start_start::inf_inf::assert(data, BodRuleSet::Strict, true);
            utils::abs::start_start::inf_inf::assert(data, BodRuleSet::Lenient, true);
            utils::abs::start_start::inf_inf::assert(data, BodRuleSet::VeryLenient, true);
            utils::abs::start_start::inf_inf::assert(data, BodRuleSet::ContinuousToFuture, true);
            utils::abs::start_start::inf_inf::assert(data, BodRuleSet::ContinuousToPast, true);
        }
    }

    mod start_end {
        use super::*;

        mod finite_finite {
            use super::*;

            #[test]
            fn before() {
                let data = FINITE_START_FINITE_END_ABS.get("before").unwrap();

                utils::abs::start_end::fin_fin::assert(data, BodRuleSet::Strict, false);
                utils::abs::start_end::fin_fin::assert(data, BodRuleSet::Lenient, false);
                utils::abs::start_end::fin_fin::assert(data, BodRuleSet::VeryLenient, false);
                utils::abs::start_end::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                utils::abs::start_end::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
            }

            mod equal {
                use super::*;

                #[test]
                fn inclusive_inclusive() {
                    let data = FINITE_START_FINITE_END_ABS.get("equal_incl_incl").unwrap();

                    utils::abs::start_end::fin_fin::assert(data, BodRuleSet::Strict, true);
                    utils::abs::start_end::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::abs::start_end::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::abs::start_end::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, true);
                    utils::abs::start_end::fin_fin::assert(data, BodRuleSet::ContinuousToPast, true);
                }

                #[test]
                fn inclusive_exclusive() {
                    let data = FINITE_START_FINITE_END_ABS.get("equal_incl_excl").unwrap();

                    utils::abs::start_end::fin_fin::assert(data, BodRuleSet::Strict, false);
                    utils::abs::start_end::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::abs::start_end::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::abs::start_end::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, true);
                    utils::abs::start_end::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
                }

                #[test]
                fn exclusive_inclusive() {
                    let data = FINITE_START_FINITE_END_ABS.get("equal_excl_incl").unwrap();

                    utils::abs::start_end::fin_fin::assert(data, BodRuleSet::Strict, false);
                    utils::abs::start_end::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::abs::start_end::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::abs::start_end::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                    utils::abs::start_end::fin_fin::assert(data, BodRuleSet::ContinuousToPast, true);
                }

                #[test]
                fn exclusive_exclusive() {
                    let data = FINITE_START_FINITE_END_ABS.get("equal_excl_excl").unwrap();

                    utils::abs::start_end::fin_fin::assert(data, BodRuleSet::Strict, false);
                    utils::abs::start_end::fin_fin::assert(data, BodRuleSet::Lenient, false);
                    utils::abs::start_end::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::abs::start_end::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                    utils::abs::start_end::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
                }
            }

            #[test]
            fn after() {
                let data = FINITE_START_FINITE_END_ABS.get("after").unwrap();

                utils::abs::start_end::fin_fin::assert(data, BodRuleSet::Strict, false);
                utils::abs::start_end::fin_fin::assert(data, BodRuleSet::Lenient, false);
                utils::abs::start_end::fin_fin::assert(data, BodRuleSet::VeryLenient, false);
                utils::abs::start_end::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                utils::abs::start_end::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
            }
        }

        #[test]
        fn finite_infinite() {
            let data = &*FINITE_START_INF_END_ABS;

            utils::abs::start_end::fin_inf::assert(data, BodRuleSet::Strict, false);
            utils::abs::start_end::fin_inf::assert(data, BodRuleSet::Lenient, false);
            utils::abs::start_end::fin_inf::assert(data, BodRuleSet::VeryLenient, false);
            utils::abs::start_end::fin_inf::assert(data, BodRuleSet::ContinuousToFuture, false);
            utils::abs::start_end::fin_inf::assert(data, BodRuleSet::ContinuousToPast, false);
        }

        #[test]
        fn infinite_finite() {
            let data = &*INF_START_FINITE_END_ABS;

            utils::abs::start_end::inf_fin::assert(data, BodRuleSet::Strict, false);
            utils::abs::start_end::inf_fin::assert(data, BodRuleSet::Lenient, false);
            utils::abs::start_end::inf_fin::assert(data, BodRuleSet::VeryLenient, false);
            utils::abs::start_end::inf_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
            utils::abs::start_end::inf_fin::assert(data, BodRuleSet::ContinuousToPast, false);
        }

        #[test]
        fn infinite_infinite() {
            let data = &*INF_START_INF_END_ABS;

            utils::abs::start_end::inf_inf::assert(data, BodRuleSet::Strict, false);
            utils::abs::start_end::inf_inf::assert(data, BodRuleSet::Lenient, false);
            utils::abs::start_end::inf_inf::assert(data, BodRuleSet::VeryLenient, false);
            utils::abs::start_end::inf_inf::assert(data, BodRuleSet::ContinuousToFuture, false);
            utils::abs::start_end::inf_inf::assert(data, BodRuleSet::ContinuousToPast, false);
        }
    }

    mod end_start {
        use super::*;

        mod finite_finite {
            use super::*;

            #[test]
            fn before() {
                let data = FINITE_END_FINITE_START_ABS.get("before").unwrap();

                utils::abs::end_start::fin_fin::assert(data, BodRuleSet::Strict, false);
                utils::abs::end_start::fin_fin::assert(data, BodRuleSet::Lenient, false);
                utils::abs::end_start::fin_fin::assert(data, BodRuleSet::VeryLenient, false);
                utils::abs::end_start::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                utils::abs::end_start::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
            }

            mod equal {
                use super::*;

                #[test]
                fn inclusive_inclusive() {
                    let data = FINITE_END_FINITE_START_ABS.get("equal_incl_incl").unwrap();

                    utils::abs::end_start::fin_fin::assert(data, BodRuleSet::Strict, true);
                    utils::abs::end_start::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::abs::end_start::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::abs::end_start::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, true);
                    utils::abs::end_start::fin_fin::assert(data, BodRuleSet::ContinuousToPast, true);
                }

                #[test]
                fn inclusive_exclusive() {
                    let data = FINITE_END_FINITE_START_ABS.get("equal_incl_excl").unwrap();

                    utils::abs::end_start::fin_fin::assert(data, BodRuleSet::Strict, false);
                    utils::abs::end_start::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::abs::end_start::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::abs::end_start::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                    utils::abs::end_start::fin_fin::assert(data, BodRuleSet::ContinuousToPast, true);
                }

                #[test]
                fn exclusive_inclusive() {
                    let data = FINITE_END_FINITE_START_ABS.get("equal_excl_incl").unwrap();

                    utils::abs::end_start::fin_fin::assert(data, BodRuleSet::Strict, false);
                    utils::abs::end_start::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::abs::end_start::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::abs::end_start::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, true);
                    utils::abs::end_start::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
                }

                #[test]
                fn exclusive_exclusive() {
                    let data = FINITE_END_FINITE_START_ABS.get("equal_excl_excl").unwrap();

                    utils::abs::end_start::fin_fin::assert(data, BodRuleSet::Strict, false);
                    utils::abs::end_start::fin_fin::assert(data, BodRuleSet::Lenient, false);
                    utils::abs::end_start::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::abs::end_start::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                    utils::abs::end_start::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
                }
            }

            #[test]
            fn after() {
                let data = FINITE_END_FINITE_START_ABS.get("after").unwrap();

                utils::abs::end_start::fin_fin::assert(data, BodRuleSet::Strict, false);
                utils::abs::end_start::fin_fin::assert(data, BodRuleSet::Lenient, false);
                utils::abs::end_start::fin_fin::assert(data, BodRuleSet::VeryLenient, false);
                utils::abs::end_start::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                utils::abs::end_start::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
            }
        }

        #[test]
        fn finite_infinite() {
            let data = &*FINITE_END_INF_START_ABS;

            utils::abs::end_start::fin_inf::assert(data, BodRuleSet::Strict, false);
            utils::abs::end_start::fin_inf::assert(data, BodRuleSet::Lenient, false);
            utils::abs::end_start::fin_inf::assert(data, BodRuleSet::VeryLenient, false);
            utils::abs::end_start::fin_inf::assert(data, BodRuleSet::ContinuousToFuture, false);
            utils::abs::end_start::fin_inf::assert(data, BodRuleSet::ContinuousToPast, false);
        }

        #[test]
        fn infinite_finite() {
            let data = &*INF_END_FINITE_START_ABS;

            utils::abs::end_start::inf_fin::assert(data, BodRuleSet::Strict, false);
            utils::abs::end_start::inf_fin::assert(data, BodRuleSet::Lenient, false);
            utils::abs::end_start::inf_fin::assert(data, BodRuleSet::VeryLenient, false);
            utils::abs::end_start::inf_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
            utils::abs::end_start::inf_fin::assert(data, BodRuleSet::ContinuousToPast, false);
        }

        #[test]
        fn infinite_infinite() {
            let data = &*INF_END_INF_START_ABS;

            utils::abs::end_start::inf_inf::assert(data, BodRuleSet::Strict, false);
            utils::abs::end_start::inf_inf::assert(data, BodRuleSet::Lenient, false);
            utils::abs::end_start::inf_inf::assert(data, BodRuleSet::VeryLenient, false);
            utils::abs::end_start::inf_inf::assert(data, BodRuleSet::ContinuousToFuture, false);
            utils::abs::end_start::inf_inf::assert(data, BodRuleSet::ContinuousToPast, false);
        }
    }

    mod end_end {
        use super::*;

        mod finite_finite {
            use super::*;

            #[test]
            fn before() {
                let data = FINITE_END_FINITE_END_ABS.get("before").unwrap();

                utils::abs::end_end::fin_fin::assert(data, BodRuleSet::Strict, false);
                utils::abs::end_end::fin_fin::assert(data, BodRuleSet::Lenient, false);
                utils::abs::end_end::fin_fin::assert(data, BodRuleSet::VeryLenient, false);
                utils::abs::end_end::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                utils::abs::end_end::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
            }

            mod equal {
                use super::*;

                #[test]
                fn inclusive_inclusive() {
                    let data = FINITE_END_FINITE_END_ABS.get("equal_incl_incl").unwrap();

                    utils::abs::end_end::fin_fin::assert(data, BodRuleSet::Strict, true);
                    utils::abs::end_end::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::abs::end_end::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::abs::end_end::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, true);
                    utils::abs::end_end::fin_fin::assert(data, BodRuleSet::ContinuousToPast, true);
                }

                #[test]
                fn inclusive_exclusive() {
                    let data = FINITE_END_FINITE_END_ABS.get("equal_incl_excl").unwrap();

                    utils::abs::end_end::fin_fin::assert(data, BodRuleSet::Strict, false);
                    utils::abs::end_end::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::abs::end_end::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::abs::end_end::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                    utils::abs::end_end::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
                }

                #[test]
                fn exclusive_inclusive() {
                    let data = FINITE_END_FINITE_END_ABS.get("equal_excl_incl").unwrap();

                    utils::abs::end_end::fin_fin::assert(data, BodRuleSet::Strict, false);
                    utils::abs::end_end::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::abs::end_end::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::abs::end_end::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                    utils::abs::end_end::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
                }

                #[test]
                fn exclusive_exclusive() {
                    let data = FINITE_END_FINITE_END_ABS.get("equal_excl_excl").unwrap();

                    utils::abs::end_end::fin_fin::assert(data, BodRuleSet::Strict, true);
                    utils::abs::end_end::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::abs::end_end::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::abs::end_end::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, true);
                    utils::abs::end_end::fin_fin::assert(data, BodRuleSet::ContinuousToPast, true);
                }
            }

            #[test]
            fn after() {
                let data = FINITE_END_FINITE_END_ABS.get("after").unwrap();

                utils::abs::end_end::fin_fin::assert(data, BodRuleSet::Strict, false);
                utils::abs::end_end::fin_fin::assert(data, BodRuleSet::Lenient, false);
                utils::abs::end_end::fin_fin::assert(data, BodRuleSet::VeryLenient, false);
                utils::abs::end_end::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                utils::abs::end_end::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
            }
        }

        #[test]
        fn finite_infinite() {
            let data = &*FINITE_END_INF_END_ABS;

            utils::abs::end_end::fin_inf::assert(data, BodRuleSet::Strict, false);
            utils::abs::end_end::fin_inf::assert(data, BodRuleSet::Lenient, false);
            utils::abs::end_end::fin_inf::assert(data, BodRuleSet::VeryLenient, false);
            utils::abs::end_end::fin_inf::assert(data, BodRuleSet::ContinuousToFuture, false);
            utils::abs::end_end::fin_inf::assert(data, BodRuleSet::ContinuousToPast, false);
        }

        #[test]
        fn infinite_finite() {
            let data = &*INF_END_FINITE_END_ABS;

            utils::abs::end_end::inf_fin::assert(data, BodRuleSet::Strict, false);
            utils::abs::end_end::inf_fin::assert(data, BodRuleSet::Lenient, false);
            utils::abs::end_end::inf_fin::assert(data, BodRuleSet::VeryLenient, false);
            utils::abs::end_end::inf_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
            utils::abs::end_end::inf_fin::assert(data, BodRuleSet::ContinuousToPast, false);
        }

        #[test]
        fn infinite_infinite() {
            let data = &*INF_END_INF_END_ABS;

            utils::abs::end_end::inf_inf::assert(data, BodRuleSet::Strict, true);
            utils::abs::end_end::inf_inf::assert(data, BodRuleSet::Lenient, true);
            utils::abs::end_end::inf_inf::assert(data, BodRuleSet::VeryLenient, true);
            utils::abs::end_end::inf_inf::assert(data, BodRuleSet::ContinuousToFuture, true);
            utils::abs::end_end::inf_inf::assert(data, BodRuleSet::ContinuousToPast, true);
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
                let data = FINITE_START_FINITE_START_REL.get("before").unwrap();

                utils::rel::start_start::fin_fin::assert(data, BodRuleSet::Strict, false);
                utils::rel::start_start::fin_fin::assert(data, BodRuleSet::Lenient, false);
                utils::rel::start_start::fin_fin::assert(data, BodRuleSet::VeryLenient, false);
                utils::rel::start_start::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                utils::rel::start_start::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
            }

            mod equal {
                use super::*;

                #[test]
                fn inclusive_inclusive() {
                    let data = FINITE_START_FINITE_START_REL.get("equal_incl_incl").unwrap();

                    utils::rel::start_start::fin_fin::assert(data, BodRuleSet::Strict, true);
                    utils::rel::start_start::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::rel::start_start::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::rel::start_start::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, true);
                    utils::rel::start_start::fin_fin::assert(data, BodRuleSet::ContinuousToPast, true);
                }

                #[test]
                fn inclusive_exclusive() {
                    let data = FINITE_START_FINITE_START_REL.get("equal_incl_excl").unwrap();

                    utils::rel::start_start::fin_fin::assert(data, BodRuleSet::Strict, false);
                    utils::rel::start_start::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::rel::start_start::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::rel::start_start::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                    utils::rel::start_start::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
                }

                #[test]
                fn exclusive_inclusive() {
                    let data = FINITE_START_FINITE_START_REL.get("equal_excl_incl").unwrap();

                    utils::rel::start_start::fin_fin::assert(data, BodRuleSet::Strict, false);
                    utils::rel::start_start::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::rel::start_start::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::rel::start_start::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                    utils::rel::start_start::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
                }

                #[test]
                fn exclusive_exclusive() {
                    let data = FINITE_START_FINITE_START_REL.get("equal_excl_excl").unwrap();

                    utils::rel::start_start::fin_fin::assert(data, BodRuleSet::Strict, true);
                    utils::rel::start_start::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::rel::start_start::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::rel::start_start::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, true);
                    utils::rel::start_start::fin_fin::assert(data, BodRuleSet::ContinuousToPast, true);
                }
            }

            #[test]
            fn after() {
                let data = FINITE_START_FINITE_START_REL.get("after").unwrap();

                utils::rel::start_start::fin_fin::assert(data, BodRuleSet::Strict, false);
                utils::rel::start_start::fin_fin::assert(data, BodRuleSet::Lenient, false);
                utils::rel::start_start::fin_fin::assert(data, BodRuleSet::VeryLenient, false);
                utils::rel::start_start::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                utils::rel::start_start::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
            }
        }

        #[test]
        fn finite_infinite() {
            let data = &*FINITE_START_INF_START_REL;

            utils::rel::start_start::fin_inf::assert(data, BodRuleSet::Strict, false);
            utils::rel::start_start::fin_inf::assert(data, BodRuleSet::Lenient, false);
            utils::rel::start_start::fin_inf::assert(data, BodRuleSet::VeryLenient, false);
            utils::rel::start_start::fin_inf::assert(data, BodRuleSet::ContinuousToFuture, false);
            utils::rel::start_start::fin_inf::assert(data, BodRuleSet::ContinuousToPast, false);
        }

        #[test]
        fn infinite_finite() {
            let data = &*INF_START_FINITE_START_REL;

            utils::rel::start_start::inf_fin::assert(data, BodRuleSet::Strict, false);
            utils::rel::start_start::inf_fin::assert(data, BodRuleSet::Lenient, false);
            utils::rel::start_start::inf_fin::assert(data, BodRuleSet::VeryLenient, false);
            utils::rel::start_start::inf_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
            utils::rel::start_start::inf_fin::assert(data, BodRuleSet::ContinuousToPast, false);
        }

        #[test]
        fn infinite_infinite() {
            let data = &*INF_START_INF_START_REL;

            utils::rel::start_start::inf_inf::assert(data, BodRuleSet::Strict, true);
            utils::rel::start_start::inf_inf::assert(data, BodRuleSet::Lenient, true);
            utils::rel::start_start::inf_inf::assert(data, BodRuleSet::VeryLenient, true);
            utils::rel::start_start::inf_inf::assert(data, BodRuleSet::ContinuousToFuture, true);
            utils::rel::start_start::inf_inf::assert(data, BodRuleSet::ContinuousToPast, true);
        }
    }

    mod start_end {
        use super::*;

        mod finite_finite {
            use super::*;

            #[test]
            fn before() {
                let data = FINITE_START_FINITE_END_REL.get("before").unwrap();

                utils::rel::start_end::fin_fin::assert(data, BodRuleSet::Strict, false);
                utils::rel::start_end::fin_fin::assert(data, BodRuleSet::Lenient, false);
                utils::rel::start_end::fin_fin::assert(data, BodRuleSet::VeryLenient, false);
                utils::rel::start_end::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                utils::rel::start_end::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
            }

            mod equal {
                use super::*;

                #[test]
                fn inclusive_inclusive() {
                    let data = FINITE_START_FINITE_END_REL.get("equal_incl_incl").unwrap();

                    utils::rel::start_end::fin_fin::assert(data, BodRuleSet::Strict, true);
                    utils::rel::start_end::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::rel::start_end::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::rel::start_end::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, true);
                    utils::rel::start_end::fin_fin::assert(data, BodRuleSet::ContinuousToPast, true);
                }

                #[test]
                fn inclusive_exclusive() {
                    let data = FINITE_START_FINITE_END_REL.get("equal_incl_excl").unwrap();

                    utils::rel::start_end::fin_fin::assert(data, BodRuleSet::Strict, false);
                    utils::rel::start_end::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::rel::start_end::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::rel::start_end::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, true);
                    utils::rel::start_end::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
                }

                #[test]
                fn exclusive_inclusive() {
                    let data = FINITE_START_FINITE_END_REL.get("equal_excl_incl").unwrap();

                    utils::rel::start_end::fin_fin::assert(data, BodRuleSet::Strict, false);
                    utils::rel::start_end::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::rel::start_end::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::rel::start_end::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                    utils::rel::start_end::fin_fin::assert(data, BodRuleSet::ContinuousToPast, true);
                }

                #[test]
                fn exclusive_exclusive() {
                    let data = FINITE_START_FINITE_END_REL.get("equal_excl_excl").unwrap();

                    utils::rel::start_end::fin_fin::assert(data, BodRuleSet::Strict, false);
                    utils::rel::start_end::fin_fin::assert(data, BodRuleSet::Lenient, false);
                    utils::rel::start_end::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::rel::start_end::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                    utils::rel::start_end::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
                }
            }

            #[test]
            fn after() {
                let data = FINITE_START_FINITE_END_REL.get("after").unwrap();

                utils::rel::start_end::fin_fin::assert(data, BodRuleSet::Strict, false);
                utils::rel::start_end::fin_fin::assert(data, BodRuleSet::Lenient, false);
                utils::rel::start_end::fin_fin::assert(data, BodRuleSet::VeryLenient, false);
                utils::rel::start_end::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                utils::rel::start_end::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
            }
        }

        #[test]
        fn finite_infinite() {
            let data = &*FINITE_START_INF_END_REL;

            utils::rel::start_end::fin_inf::assert(data, BodRuleSet::Strict, false);
            utils::rel::start_end::fin_inf::assert(data, BodRuleSet::Lenient, false);
            utils::rel::start_end::fin_inf::assert(data, BodRuleSet::VeryLenient, false);
            utils::rel::start_end::fin_inf::assert(data, BodRuleSet::ContinuousToFuture, false);
            utils::rel::start_end::fin_inf::assert(data, BodRuleSet::ContinuousToPast, false);
        }

        #[test]
        fn infinite_finite() {
            let data = &*INF_START_FINITE_END_REL;

            utils::rel::start_end::inf_fin::assert(data, BodRuleSet::Strict, false);
            utils::rel::start_end::inf_fin::assert(data, BodRuleSet::Lenient, false);
            utils::rel::start_end::inf_fin::assert(data, BodRuleSet::VeryLenient, false);
            utils::rel::start_end::inf_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
            utils::rel::start_end::inf_fin::assert(data, BodRuleSet::ContinuousToPast, false);
        }

        #[test]
        fn infinite_infinite() {
            let data = &*INF_START_INF_END_REL;

            utils::rel::start_end::inf_inf::assert(data, BodRuleSet::Strict, false);
            utils::rel::start_end::inf_inf::assert(data, BodRuleSet::Lenient, false);
            utils::rel::start_end::inf_inf::assert(data, BodRuleSet::VeryLenient, false);
            utils::rel::start_end::inf_inf::assert(data, BodRuleSet::ContinuousToFuture, false);
            utils::rel::start_end::inf_inf::assert(data, BodRuleSet::ContinuousToPast, false);
        }
    }

    mod end_start {
        use super::*;

        mod finite_finite {
            use super::*;

            #[test]
            fn before() {
                let data = FINITE_END_FINITE_START_REL.get("before").unwrap();

                utils::rel::end_start::fin_fin::assert(data, BodRuleSet::Strict, false);
                utils::rel::end_start::fin_fin::assert(data, BodRuleSet::Lenient, false);
                utils::rel::end_start::fin_fin::assert(data, BodRuleSet::VeryLenient, false);
                utils::rel::end_start::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                utils::rel::end_start::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
            }

            mod equal {
                use super::*;

                #[test]
                fn inclusive_inclusive() {
                    let data = FINITE_END_FINITE_START_REL.get("equal_incl_incl").unwrap();

                    utils::rel::end_start::fin_fin::assert(data, BodRuleSet::Strict, true);
                    utils::rel::end_start::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::rel::end_start::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::rel::end_start::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, true);
                    utils::rel::end_start::fin_fin::assert(data, BodRuleSet::ContinuousToPast, true);
                }

                #[test]
                fn inclusive_exclusive() {
                    let data = FINITE_END_FINITE_START_REL.get("equal_incl_excl").unwrap();

                    utils::rel::end_start::fin_fin::assert(data, BodRuleSet::Strict, false);
                    utils::rel::end_start::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::rel::end_start::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::rel::end_start::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                    utils::rel::end_start::fin_fin::assert(data, BodRuleSet::ContinuousToPast, true);
                }

                #[test]
                fn exclusive_inclusive() {
                    let data = FINITE_END_FINITE_START_REL.get("equal_excl_incl").unwrap();

                    utils::rel::end_start::fin_fin::assert(data, BodRuleSet::Strict, false);
                    utils::rel::end_start::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::rel::end_start::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::rel::end_start::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, true);
                    utils::rel::end_start::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
                }

                #[test]
                fn exclusive_exclusive() {
                    let data = FINITE_END_FINITE_START_REL.get("equal_excl_excl").unwrap();

                    utils::rel::end_start::fin_fin::assert(data, BodRuleSet::Strict, false);
                    utils::rel::end_start::fin_fin::assert(data, BodRuleSet::Lenient, false);
                    utils::rel::end_start::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::rel::end_start::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                    utils::rel::end_start::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
                }
            }

            #[test]
            fn after() {
                let data = FINITE_END_FINITE_START_REL.get("after").unwrap();

                utils::rel::end_start::fin_fin::assert(data, BodRuleSet::Strict, false);
                utils::rel::end_start::fin_fin::assert(data, BodRuleSet::Lenient, false);
                utils::rel::end_start::fin_fin::assert(data, BodRuleSet::VeryLenient, false);
                utils::rel::end_start::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                utils::rel::end_start::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
            }
        }

        #[test]
        fn finite_infinite() {
            let data = &*FINITE_END_INF_START_REL;

            utils::rel::end_start::fin_inf::assert(data, BodRuleSet::Strict, false);
            utils::rel::end_start::fin_inf::assert(data, BodRuleSet::Lenient, false);
            utils::rel::end_start::fin_inf::assert(data, BodRuleSet::VeryLenient, false);
            utils::rel::end_start::fin_inf::assert(data, BodRuleSet::ContinuousToFuture, false);
            utils::rel::end_start::fin_inf::assert(data, BodRuleSet::ContinuousToPast, false);
        }

        #[test]
        fn infinite_finite() {
            let data = &*INF_END_FINITE_START_REL;

            utils::rel::end_start::inf_fin::assert(data, BodRuleSet::Strict, false);
            utils::rel::end_start::inf_fin::assert(data, BodRuleSet::Lenient, false);
            utils::rel::end_start::inf_fin::assert(data, BodRuleSet::VeryLenient, false);
            utils::rel::end_start::inf_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
            utils::rel::end_start::inf_fin::assert(data, BodRuleSet::ContinuousToPast, false);
        }

        #[test]
        fn infinite_infinite() {
            let data = &*INF_END_INF_START_REL;

            utils::rel::end_start::inf_inf::assert(data, BodRuleSet::Strict, false);
            utils::rel::end_start::inf_inf::assert(data, BodRuleSet::Lenient, false);
            utils::rel::end_start::inf_inf::assert(data, BodRuleSet::VeryLenient, false);
            utils::rel::end_start::inf_inf::assert(data, BodRuleSet::ContinuousToFuture, false);
            utils::rel::end_start::inf_inf::assert(data, BodRuleSet::ContinuousToPast, false);
        }
    }

    mod end_end {
        use super::*;

        mod finite_finite {
            use super::*;

            #[test]
            fn before() {
                let data = FINITE_END_FINITE_END_REL.get("before").unwrap();

                utils::rel::end_end::fin_fin::assert(data, BodRuleSet::Strict, false);
                utils::rel::end_end::fin_fin::assert(data, BodRuleSet::Lenient, false);
                utils::rel::end_end::fin_fin::assert(data, BodRuleSet::VeryLenient, false);
                utils::rel::end_end::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                utils::rel::end_end::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
            }

            mod equal {
                use super::*;

                #[test]
                fn inclusive_inclusive() {
                    let data = FINITE_END_FINITE_END_REL.get("equal_incl_incl").unwrap();

                    utils::rel::end_end::fin_fin::assert(data, BodRuleSet::Strict, true);
                    utils::rel::end_end::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::rel::end_end::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::rel::end_end::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, true);
                    utils::rel::end_end::fin_fin::assert(data, BodRuleSet::ContinuousToPast, true);
                }

                #[test]
                fn inclusive_exclusive() {
                    let data = FINITE_END_FINITE_END_REL.get("equal_incl_excl").unwrap();

                    utils::rel::end_end::fin_fin::assert(data, BodRuleSet::Strict, false);
                    utils::rel::end_end::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::rel::end_end::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::rel::end_end::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                    utils::rel::end_end::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
                }

                #[test]
                fn exclusive_inclusive() {
                    let data = FINITE_END_FINITE_END_REL.get("equal_excl_incl").unwrap();

                    utils::rel::end_end::fin_fin::assert(data, BodRuleSet::Strict, false);
                    utils::rel::end_end::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::rel::end_end::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::rel::end_end::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                    utils::rel::end_end::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
                }

                #[test]
                fn exclusive_exclusive() {
                    let data = FINITE_END_FINITE_END_REL.get("equal_excl_excl").unwrap();

                    utils::rel::end_end::fin_fin::assert(data, BodRuleSet::Strict, true);
                    utils::rel::end_end::fin_fin::assert(data, BodRuleSet::Lenient, true);
                    utils::rel::end_end::fin_fin::assert(data, BodRuleSet::VeryLenient, true);
                    utils::rel::end_end::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, true);
                    utils::rel::end_end::fin_fin::assert(data, BodRuleSet::ContinuousToPast, true);
                }
            }

            #[test]
            fn after() {
                let data = FINITE_END_FINITE_END_REL.get("after").unwrap();

                utils::rel::end_end::fin_fin::assert(data, BodRuleSet::Strict, false);
                utils::rel::end_end::fin_fin::assert(data, BodRuleSet::Lenient, false);
                utils::rel::end_end::fin_fin::assert(data, BodRuleSet::VeryLenient, false);
                utils::rel::end_end::fin_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
                utils::rel::end_end::fin_fin::assert(data, BodRuleSet::ContinuousToPast, false);
            }
        }

        #[test]
        fn finite_infinite() {
            let data = &*FINITE_END_INF_END_REL;

            utils::rel::end_end::fin_inf::assert(data, BodRuleSet::Strict, false);
            utils::rel::end_end::fin_inf::assert(data, BodRuleSet::Lenient, false);
            utils::rel::end_end::fin_inf::assert(data, BodRuleSet::VeryLenient, false);
            utils::rel::end_end::fin_inf::assert(data, BodRuleSet::ContinuousToFuture, false);
            utils::rel::end_end::fin_inf::assert(data, BodRuleSet::ContinuousToPast, false);
        }

        #[test]
        fn infinite_finite() {
            let data = &*INF_END_FINITE_END_REL;

            utils::rel::end_end::inf_fin::assert(data, BodRuleSet::Strict, false);
            utils::rel::end_end::inf_fin::assert(data, BodRuleSet::Lenient, false);
            utils::rel::end_end::inf_fin::assert(data, BodRuleSet::VeryLenient, false);
            utils::rel::end_end::inf_fin::assert(data, BodRuleSet::ContinuousToFuture, false);
            utils::rel::end_end::inf_fin::assert(data, BodRuleSet::ContinuousToPast, false);
        }

        #[test]
        fn infinite_infinite() {
            let data = &*INF_END_INF_END_REL;

            utils::rel::end_end::inf_inf::assert(data, BodRuleSet::Strict, true);
            utils::rel::end_end::inf_inf::assert(data, BodRuleSet::Lenient, true);
            utils::rel::end_end::inf_inf::assert(data, BodRuleSet::VeryLenient, true);
            utils::rel::end_end::inf_inf::assert(data, BodRuleSet::ContinuousToFuture, true);
            utils::rel::end_end::inf_inf::assert(data, BodRuleSet::ContinuousToPast, true);
        }
    }
}
