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

mod utils {
    use super::*;

    const RULE_SETS: [BodRuleSet; 5] = [
        BodRuleSet::Strict,
        BodRuleSet::Lenient,
        BodRuleSet::VeryLenient,
        BodRuleSet::ContinuousToFuture,
        BodRuleSet::ContinuousToPast,
    ];

    pub mod abs {
        use super::*;

        pub mod start_start {
            use super::*;

            pub mod fin_fin {
                use super::*;

                #[allow(clippy::too_many_lines)]
                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<AbsFiniteStartBound, AbsFiniteStartBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_start_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_start_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_finite_bound()
                                .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_finite_bound()
                                .bound_eq(&data.rhs().to_start_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_start_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_start_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_start_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_start_bound()
                                .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_start_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_start_bound()
                                .bound_eq(&data.rhs().to_start_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_start_bound(),
                            data.rhs().to_start_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_start_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_start_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_start_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_start_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }

            pub mod fin_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<AbsFiniteStartBound, AbsStartBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_start_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_start_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_start_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_start_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }

            pub mod inf_fin {
                use super::*;

                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<AbsStartBound, AbsFiniteStartBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_start_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_start_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_start_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_start_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }

            pub mod inf_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<AbsStartBound, AbsStartBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }
        }

        pub mod start_end {
            use super::*;

            pub mod fin_fin {
                use super::*;

                #[allow(clippy::too_many_lines)]
                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<AbsFiniteStartBound, AbsFiniteEndBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_end_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_end_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_finite_bound()
                                .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_finite_bound()
                                .bound_eq(&data.rhs().to_end_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_end_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_start_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_start_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_start_bound()
                                .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_start_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_start_bound()
                                .bound_eq(&data.rhs().to_end_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_start_bound(),
                            data.rhs().to_end_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_start_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_start_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_end_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_end_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }

            pub mod fin_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<AbsFiniteStartBound, AbsEndBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_start_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_start_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_start_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_start_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }

            pub mod inf_fin {
                use super::*;

                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<AbsStartBound, AbsFiniteEndBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_end_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_end_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_end_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_end_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }

            pub mod inf_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<AbsStartBound, AbsEndBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }
        }

        pub mod end_start {
            use super::*;

            pub mod fin_fin {
                use super::*;

                #[allow(clippy::too_many_lines)]
                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<AbsFiniteEndBound, AbsFiniteStartBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_start_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_start_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_finite_bound()
                                .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_finite_bound()
                                .bound_eq(&data.rhs().to_start_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_start_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_end_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_end_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_end_bound()
                                .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_end_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_end_bound()
                                .bound_eq(&data.rhs().to_start_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_end_bound(),
                            data.rhs().to_start_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_end_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_end_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_start_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_start_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }

            pub mod fin_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<AbsFiniteEndBound, AbsStartBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_end_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_end_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_end_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_end_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }

            pub mod inf_fin {
                use super::*;

                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<AbsEndBound, AbsFiniteStartBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_start_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_start_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_start_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_start_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }

            pub mod inf_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<AbsEndBound, AbsStartBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }
        }

        pub mod end_end {
            use super::*;

            pub mod fin_fin {
                use super::*;

                #[allow(clippy::too_many_lines)]
                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<AbsFiniteEndBound, AbsFiniteEndBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_end_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_end_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_finite_bound()
                                .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_finite_bound()
                                .bound_eq(&data.rhs().to_end_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_end_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_end_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_end_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_end_bound()
                                .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_end_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_end_bound().bound_eq(&data.rhs().to_end_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_end_bound(),
                            data.rhs().to_end_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_end_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_end_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_end_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_end_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }

            pub mod fin_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<AbsFiniteEndBound, AbsEndBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_end_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_end_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_end_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_end_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }

            pub mod inf_fin {
                use super::*;

                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<AbsEndBound, AbsFiniteEndBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_end_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_end_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_end_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_end_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }

            pub mod inf_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<AbsEndBound, AbsEndBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
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
                pub fn assert<F>(data: &BinOpPair<RelFiniteStartBound, RelFiniteStartBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_start_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_start_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_finite_bound()
                                .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_finite_bound()
                                .bound_eq(&data.rhs().to_start_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_start_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_start_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_start_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_start_bound()
                                .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_start_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_start_bound()
                                .bound_eq(&data.rhs().to_start_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_start_bound(),
                            data.rhs().to_start_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_start_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_start_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_start_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_start_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }

            pub mod fin_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<RelFiniteStartBound, RelStartBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_start_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_start_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_start_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_start_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }

            pub mod inf_fin {
                use super::*;

                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<RelStartBound, RelFiniteStartBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_start_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_start_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_start_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_start_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }

            pub mod inf_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<RelStartBound, RelStartBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }
        }

        pub mod start_end {
            use super::*;

            pub mod fin_fin {
                use super::*;

                #[allow(clippy::too_many_lines)]
                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<RelFiniteStartBound, RelFiniteEndBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_end_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_end_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_finite_bound()
                                .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_finite_bound()
                                .bound_eq(&data.rhs().to_end_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_end_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_start_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_start_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_start_bound()
                                .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_start_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_start_bound()
                                .bound_eq(&data.rhs().to_end_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_start_bound(),
                            data.rhs().to_end_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_start_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_start_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_end_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_end_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }

            pub mod fin_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<RelFiniteStartBound, RelEndBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_start_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_start_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_start_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_start_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }

            pub mod inf_fin {
                use super::*;

                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<RelStartBound, RelFiniteEndBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_end_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_end_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_end_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_end_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }

            pub mod inf_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<RelStartBound, RelEndBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }
        }

        pub mod end_start {
            use super::*;

            pub mod fin_fin {
                use super::*;

                #[allow(clippy::too_many_lines)]
                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<RelFiniteEndBound, RelFiniteStartBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_start_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_start_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_finite_bound()
                                .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_finite_bound()
                                .bound_eq(&data.rhs().to_start_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_start_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_end_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_end_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_end_bound()
                                .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_end_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_end_bound()
                                .bound_eq(&data.rhs().to_start_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_end_bound(),
                            data.rhs().to_start_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_end_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_end_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_start_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_start_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }

            pub mod fin_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<RelFiniteEndBound, RelStartBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_end_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_end_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_end_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_end_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }

            pub mod inf_fin {
                use super::*;

                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<RelEndBound, RelFiniteStartBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_start_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_start_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_start_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_start_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }

            pub mod inf_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<RelEndBound, RelStartBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }
        }

        pub mod end_end {
            use super::*;

            pub mod fin_fin {
                use super::*;

                #[allow(clippy::too_many_lines)]
                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<RelFiniteEndBound, RelFiniteEndBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_end_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_end_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_finite_bound()
                                .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_finite_bound()
                                .bound_eq(&data.rhs().to_end_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_end_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_end_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_end_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs()
                                .to_end_bound()
                                .bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_end_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_end_bound().bound_eq(&data.rhs().to_end_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_end_bound(),
                            data.rhs().to_end_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_end_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_end_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_end_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_end_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }

            pub mod fin_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<RelFiniteEndBound, RelEndBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_finite_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_finite_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_end_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_end_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_end_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_end_bound(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }

            pub mod inf_fin {
                use super::*;

                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<RelEndBound, RelFiniteEndBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_end_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_end_bound(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_finite_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_finite_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_end_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_end_bound(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
                }
            }

            pub mod inf_inf {
                use super::*;

                #[track_caller]
                pub fn assert<F>(data: &BinOpPair<RelEndBound, RelEndBound>, mut expected_f: F)
                where
                    F: FnMut(BodRuleSet) -> bool,
                {
                    for rule_set in RULE_SETS {
                        assert_eq!(
                            data.lhs().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs(),
                            data.rhs().to_bound(),
                        );

                        assert_eq!(
                            data.lhs().to_bound().bound_eq(data.rhs(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs(),
                        );
                        assert_eq!(
                            data.lhs().to_bound().bound_eq(&data.rhs().to_bound(), rule_set),
                            expected_f(rule_set),
                            "Equality between {:#?} and {:#?}",
                            data.lhs().to_bound(),
                            data.rhs().to_bound(),
                        );
                    }
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
                utils::abs::start_start::fin_fin::assert(FINITE_START_FINITE_START_ABS.get("before").unwrap(), |_| {
                    false
                });
            }

            mod equal {
                use super::*;

                #[test]
                fn inclusive_inclusive() {
                    utils::abs::start_start::fin_fin::assert(
                        FINITE_START_FINITE_START_ABS.get("equal_incl_incl").unwrap(),
                        |_| true,
                    );
                }

                #[test]
                fn inclusive_exclusive() {
                    utils::abs::start_start::fin_fin::assert(
                        FINITE_START_FINITE_START_ABS.get("equal_incl_excl").unwrap(),
                        |rule_set| matches!(rule_set, BodRuleSet::Lenient | BodRuleSet::VeryLenient),
                    );
                }

                #[test]
                fn exclusive_inclusive() {
                    utils::abs::start_start::fin_fin::assert(
                        FINITE_START_FINITE_START_ABS.get("equal_excl_incl").unwrap(),
                        |rule_set| matches!(rule_set, BodRuleSet::Lenient | BodRuleSet::VeryLenient),
                    );
                }

                #[test]
                fn exclusive_exclusive() {
                    utils::abs::start_start::fin_fin::assert(
                        FINITE_START_FINITE_START_ABS.get("equal_excl_excl").unwrap(),
                        |_| true,
                    );
                }
            }

            #[test]
            fn after() {
                utils::abs::start_start::fin_fin::assert(FINITE_START_FINITE_START_ABS.get("after").unwrap(), |_| {
                    false
                });
            }
        }

        #[test]
        fn finite_infinite() {
            utils::abs::start_start::fin_inf::assert(&FINITE_START_INF_START_ABS, |_| false);
        }

        #[test]
        fn infinite_finite() {
            utils::abs::start_start::inf_fin::assert(&INF_START_FINITE_START_ABS, |_| false);
        }

        #[test]
        fn infinite_infinite() {
            utils::abs::start_start::inf_inf::assert(&INF_START_INF_START_ABS, |_| true);
        }
    }

    mod start_end {
        use super::*;

        mod finite_finite {
            use super::*;

            #[test]
            fn before() {
                utils::abs::start_end::fin_fin::assert(FINITE_START_FINITE_END_ABS.get("before").unwrap(), |_| false);
            }

            mod equal {
                use super::*;

                #[test]
                fn inclusive_inclusive() {
                    utils::abs::start_end::fin_fin::assert(
                        FINITE_START_FINITE_END_ABS.get("equal_incl_incl").unwrap(),
                        |_| true,
                    );
                }

                #[test]
                fn inclusive_exclusive() {
                    utils::abs::start_end::fin_fin::assert(
                        FINITE_START_FINITE_END_ABS.get("equal_incl_excl").unwrap(),
                        |rule_set| {
                            matches!(
                                rule_set,
                                BodRuleSet::Lenient | BodRuleSet::VeryLenient | BodRuleSet::ContinuousToFuture
                            )
                        },
                    );
                }

                #[test]
                fn exclusive_inclusive() {
                    utils::abs::start_end::fin_fin::assert(
                        FINITE_START_FINITE_END_ABS.get("equal_excl_incl").unwrap(),
                        |rule_set| {
                            matches!(
                                rule_set,
                                BodRuleSet::Lenient | BodRuleSet::VeryLenient | BodRuleSet::ContinuousToPast
                            )
                        },
                    );
                }

                #[test]
                fn exclusive_exclusive() {
                    utils::abs::start_end::fin_fin::assert(
                        FINITE_START_FINITE_END_ABS.get("equal_excl_excl").unwrap(),
                        |rule_set| matches!(rule_set, BodRuleSet::VeryLenient),
                    );
                }
            }

            #[test]
            fn after() {
                utils::abs::start_end::fin_fin::assert(FINITE_START_FINITE_END_ABS.get("after").unwrap(), |_| false);
            }
        }

        #[test]
        fn finite_infinite() {
            utils::abs::start_end::fin_inf::assert(&FINITE_START_INF_END_ABS, |_| false);
        }

        #[test]
        fn infinite_finite() {
            utils::abs::start_end::inf_fin::assert(&INF_START_FINITE_END_ABS, |_| false);
        }

        #[test]
        fn infinite_infinite() {
            utils::abs::start_end::inf_inf::assert(&INF_START_INF_END_ABS, |_| false);
        }
    }

    mod end_start {
        use super::*;

        mod finite_finite {
            use super::*;

            #[test]
            fn before() {
                utils::abs::end_start::fin_fin::assert(FINITE_END_FINITE_START_ABS.get("before").unwrap(), |_| false);
            }

            mod equal {
                use super::*;

                #[test]
                fn inclusive_inclusive() {
                    utils::abs::end_start::fin_fin::assert(
                        FINITE_END_FINITE_START_ABS.get("equal_incl_incl").unwrap(),
                        |_| true,
                    );
                }

                #[test]
                fn inclusive_exclusive() {
                    utils::abs::end_start::fin_fin::assert(
                        FINITE_END_FINITE_START_ABS.get("equal_incl_excl").unwrap(),
                        |rule_set| {
                            matches!(
                                rule_set,
                                BodRuleSet::Lenient | BodRuleSet::VeryLenient | BodRuleSet::ContinuousToPast
                            )
                        },
                    );
                }

                #[test]
                fn exclusive_inclusive() {
                    utils::abs::end_start::fin_fin::assert(
                        FINITE_END_FINITE_START_ABS.get("equal_excl_incl").unwrap(),
                        |rule_set| {
                            matches!(
                                rule_set,
                                BodRuleSet::Lenient | BodRuleSet::VeryLenient | BodRuleSet::ContinuousToFuture
                            )
                        },
                    );
                }

                #[test]
                fn exclusive_exclusive() {
                    utils::abs::end_start::fin_fin::assert(
                        FINITE_END_FINITE_START_ABS.get("equal_excl_excl").unwrap(),
                        |rule_set| matches!(rule_set, BodRuleSet::VeryLenient),
                    );
                }
            }

            #[test]
            fn after() {
                utils::abs::end_start::fin_fin::assert(FINITE_END_FINITE_START_ABS.get("after").unwrap(), |_| false);
            }
        }

        #[test]
        fn finite_infinite() {
            utils::abs::end_start::fin_inf::assert(&FINITE_END_INF_START_ABS, |_| false);
        }

        #[test]
        fn infinite_finite() {
            utils::abs::end_start::inf_fin::assert(&INF_END_FINITE_START_ABS, |_| false);
        }

        #[test]
        fn infinite_infinite() {
            utils::abs::end_start::inf_inf::assert(&INF_END_INF_START_ABS, |_| false);
        }
    }

    mod end_end {
        use super::*;

        mod finite_finite {
            use super::*;

            #[test]
            fn before() {
                utils::abs::end_end::fin_fin::assert(FINITE_END_FINITE_END_ABS.get("before").unwrap(), |_| false);
            }

            mod equal {
                use super::*;

                #[test]
                fn inclusive_inclusive() {
                    utils::abs::end_end::fin_fin::assert(
                        FINITE_END_FINITE_END_ABS.get("equal_incl_incl").unwrap(),
                        |_| true,
                    );
                }

                #[test]
                fn inclusive_exclusive() {
                    utils::abs::end_end::fin_fin::assert(
                        FINITE_END_FINITE_END_ABS.get("equal_incl_excl").unwrap(),
                        |rule_set| matches!(rule_set, BodRuleSet::Lenient | BodRuleSet::VeryLenient),
                    );
                }

                #[test]
                fn exclusive_inclusive() {
                    utils::abs::end_end::fin_fin::assert(
                        FINITE_END_FINITE_END_ABS.get("equal_excl_incl").unwrap(),
                        |rule_set| matches!(rule_set, BodRuleSet::Lenient | BodRuleSet::VeryLenient),
                    );
                }

                #[test]
                fn exclusive_exclusive() {
                    utils::abs::end_end::fin_fin::assert(
                        FINITE_END_FINITE_END_ABS.get("equal_excl_excl").unwrap(),
                        |_| true,
                    );
                }
            }

            #[test]
            fn after() {
                utils::abs::end_end::fin_fin::assert(FINITE_END_FINITE_END_ABS.get("after").unwrap(), |_| false);
            }
        }

        #[test]
        fn finite_infinite() {
            utils::abs::end_end::fin_inf::assert(&FINITE_END_INF_END_ABS, |_| false);
        }

        #[test]
        fn infinite_finite() {
            utils::abs::end_end::inf_fin::assert(&INF_END_FINITE_END_ABS, |_| false);
        }

        #[test]
        fn infinite_infinite() {
            utils::abs::end_end::inf_inf::assert(&INF_END_INF_END_ABS, |_| true);
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
                utils::rel::start_start::fin_fin::assert(FINITE_START_FINITE_START_REL.get("before").unwrap(), |_| {
                    false
                });
            }

            mod equal {
                use super::*;

                #[test]
                fn inclusive_inclusive() {
                    utils::rel::start_start::fin_fin::assert(
                        FINITE_START_FINITE_START_REL.get("equal_incl_incl").unwrap(),
                        |_| true,
                    );
                }

                #[test]
                fn inclusive_exclusive() {
                    utils::rel::start_start::fin_fin::assert(
                        FINITE_START_FINITE_START_REL.get("equal_incl_excl").unwrap(),
                        |rule_set| matches!(rule_set, BodRuleSet::Lenient | BodRuleSet::VeryLenient),
                    );
                }

                #[test]
                fn exclusive_inclusive() {
                    utils::rel::start_start::fin_fin::assert(
                        FINITE_START_FINITE_START_REL.get("equal_excl_incl").unwrap(),
                        |rule_set| matches!(rule_set, BodRuleSet::Lenient | BodRuleSet::VeryLenient),
                    );
                }

                #[test]
                fn exclusive_exclusive() {
                    utils::rel::start_start::fin_fin::assert(
                        FINITE_START_FINITE_START_REL.get("equal_excl_excl").unwrap(),
                        |_| true,
                    );
                }
            }

            #[test]
            fn after() {
                utils::rel::start_start::fin_fin::assert(FINITE_START_FINITE_START_REL.get("after").unwrap(), |_| {
                    false
                });
            }
        }

        #[test]
        fn finite_infinite() {
            utils::rel::start_start::fin_inf::assert(&FINITE_START_INF_START_REL, |_| false);
        }

        #[test]
        fn infinite_finite() {
            utils::rel::start_start::inf_fin::assert(&INF_START_FINITE_START_REL, |_| false);
        }

        #[test]
        fn infinite_infinite() {
            utils::rel::start_start::inf_inf::assert(&INF_START_INF_START_REL, |_| true);
        }
    }

    mod start_end {
        use super::*;

        mod finite_finite {
            use super::*;

            #[test]
            fn before() {
                utils::rel::start_end::fin_fin::assert(FINITE_START_FINITE_END_REL.get("before").unwrap(), |_| false);
            }

            mod equal {
                use super::*;

                #[test]
                fn inclusive_inclusive() {
                    utils::rel::start_end::fin_fin::assert(
                        FINITE_START_FINITE_END_REL.get("equal_incl_incl").unwrap(),
                        |_| true,
                    );
                }

                #[test]
                fn inclusive_exclusive() {
                    utils::rel::start_end::fin_fin::assert(
                        FINITE_START_FINITE_END_REL.get("equal_incl_excl").unwrap(),
                        |rule_set| {
                            matches!(
                                rule_set,
                                BodRuleSet::Lenient | BodRuleSet::VeryLenient | BodRuleSet::ContinuousToFuture
                            )
                        },
                    );
                }

                #[test]
                fn exclusive_inclusive() {
                    utils::rel::start_end::fin_fin::assert(
                        FINITE_START_FINITE_END_REL.get("equal_excl_incl").unwrap(),
                        |rule_set| {
                            matches!(
                                rule_set,
                                BodRuleSet::Lenient | BodRuleSet::VeryLenient | BodRuleSet::ContinuousToPast
                            )
                        },
                    );
                }

                #[test]
                fn exclusive_exclusive() {
                    utils::rel::start_end::fin_fin::assert(
                        FINITE_START_FINITE_END_REL.get("equal_excl_excl").unwrap(),
                        |rule_set| matches!(rule_set, BodRuleSet::VeryLenient),
                    );
                }
            }

            #[test]
            fn after() {
                utils::rel::start_end::fin_fin::assert(FINITE_START_FINITE_END_REL.get("after").unwrap(), |_| false);
            }
        }

        #[test]
        fn finite_infinite() {
            utils::rel::start_end::fin_inf::assert(&FINITE_START_INF_END_REL, |_| false);
        }

        #[test]
        fn infinite_finite() {
            utils::rel::start_end::inf_fin::assert(&INF_START_FINITE_END_REL, |_| false);
        }

        #[test]
        fn infinite_infinite() {
            utils::rel::start_end::inf_inf::assert(&INF_START_INF_END_REL, |_| false);
        }
    }

    mod end_start {
        use super::*;

        mod finite_finite {
            use super::*;

            #[test]
            fn before() {
                utils::rel::end_start::fin_fin::assert(FINITE_END_FINITE_START_REL.get("before").unwrap(), |_| false);
            }

            mod equal {
                use super::*;

                #[test]
                fn inclusive_inclusive() {
                    utils::rel::end_start::fin_fin::assert(
                        FINITE_END_FINITE_START_REL.get("equal_incl_incl").unwrap(),
                        |_| true,
                    );
                }

                #[test]
                fn inclusive_exclusive() {
                    utils::rel::end_start::fin_fin::assert(
                        FINITE_END_FINITE_START_REL.get("equal_incl_excl").unwrap(),
                        |rule_set| {
                            matches!(
                                rule_set,
                                BodRuleSet::Lenient | BodRuleSet::VeryLenient | BodRuleSet::ContinuousToPast
                            )
                        },
                    );
                }

                #[test]
                fn exclusive_inclusive() {
                    utils::rel::end_start::fin_fin::assert(
                        FINITE_END_FINITE_START_REL.get("equal_excl_incl").unwrap(),
                        |rule_set| {
                            matches!(
                                rule_set,
                                BodRuleSet::Lenient | BodRuleSet::VeryLenient | BodRuleSet::ContinuousToFuture
                            )
                        },
                    );
                }

                #[test]
                fn exclusive_exclusive() {
                    utils::rel::end_start::fin_fin::assert(
                        FINITE_END_FINITE_START_REL.get("equal_excl_excl").unwrap(),
                        |rule_set| matches!(rule_set, BodRuleSet::VeryLenient),
                    );
                }
            }

            #[test]
            fn after() {
                utils::rel::end_start::fin_fin::assert(FINITE_END_FINITE_START_REL.get("after").unwrap(), |_| false);
            }
        }

        #[test]
        fn finite_infinite() {
            utils::rel::end_start::fin_inf::assert(&FINITE_END_INF_START_REL, |_| false);
        }

        #[test]
        fn infinite_finite() {
            utils::rel::end_start::inf_fin::assert(&INF_END_FINITE_START_REL, |_| false);
        }

        #[test]
        fn infinite_infinite() {
            utils::rel::end_start::inf_inf::assert(&INF_END_INF_START_REL, |_| false);
        }
    }

    mod end_end {
        use super::*;

        mod finite_finite {
            use super::*;

            #[test]
            fn before() {
                utils::rel::end_end::fin_fin::assert(FINITE_END_FINITE_END_REL.get("before").unwrap(), |_| false);
            }

            mod equal {
                use super::*;

                #[test]
                fn inclusive_inclusive() {
                    utils::rel::end_end::fin_fin::assert(
                        FINITE_END_FINITE_END_REL.get("equal_incl_incl").unwrap(),
                        |_| true,
                    );
                }

                #[test]
                fn inclusive_exclusive() {
                    utils::rel::end_end::fin_fin::assert(
                        FINITE_END_FINITE_END_REL.get("equal_incl_excl").unwrap(),
                        |rule_set| matches!(rule_set, BodRuleSet::Lenient | BodRuleSet::VeryLenient),
                    );
                }

                #[test]
                fn exclusive_inclusive() {
                    utils::rel::end_end::fin_fin::assert(
                        FINITE_END_FINITE_END_REL.get("equal_excl_incl").unwrap(),
                        |rule_set| matches!(rule_set, BodRuleSet::Lenient | BodRuleSet::VeryLenient),
                    );
                }

                #[test]
                fn exclusive_exclusive() {
                    utils::rel::end_end::fin_fin::assert(
                        FINITE_END_FINITE_END_REL.get("equal_excl_excl").unwrap(),
                        |_| true,
                    );
                }
            }

            #[test]
            fn after() {
                utils::rel::end_end::fin_fin::assert(FINITE_END_FINITE_END_REL.get("after").unwrap(), |_| false);
            }
        }

        #[test]
        fn finite_infinite() {
            utils::rel::end_end::fin_inf::assert(&FINITE_END_INF_END_REL, |_| false);
        }

        #[test]
        fn infinite_finite() {
            utils::rel::end_end::inf_fin::assert(&INF_END_FINITE_END_REL, |_| false);
        }

        #[test]
        fn infinite_infinite() {
            utils::rel::end_end::inf_inf::assert(&INF_END_INF_END_REL, |_| true);
        }
    }
}
