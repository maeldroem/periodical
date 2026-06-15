use super::absolute::*;
use crate::intervals::meta::BoundInclusivity;
use crate::test_data::date_timestamp;

mod swap_abs_finite_start_end_bounds {
    use super::*;

    #[test]
    fn ok() {
        let mut start = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
            .to_finite_start_bound();
        let mut end = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Inclusive)
            .to_finite_end_bound();

        swap_abs_finite_start_end_bounds(&mut start, &mut end);

        assert_eq!(
            start,
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Inclusive)
                .to_finite_start_bound()
        );
        assert_eq!(
            end,
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                .to_finite_end_bound()
        );
    }
}

mod swap_abs_start_end_bounds {
    use super::*;

    #[test]
    fn finite_finite() {
        let mut start =
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive).to_start_bound();
        let mut end =
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Inclusive).to_end_bound();

        swap_abs_start_end_bounds(&mut start, &mut end);

        assert_eq!(
            start,
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Inclusive).to_start_bound()
        );
        assert_eq!(
            end,
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive).to_end_bound()
        );
    }

    #[test]
    fn finite_infinite() {
        let mut start =
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive).to_start_bound();
        let mut end = AbsEndBound::InfiniteFuture;

        swap_abs_start_end_bounds(&mut start, &mut end);

        assert_eq!(start, AbsStartBound::InfinitePast);
        assert_eq!(
            end,
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive).to_end_bound()
        );
    }

    #[test]
    fn infinite_finite() {
        let mut start = AbsStartBound::InfinitePast;
        let mut end =
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive).to_end_bound();

        swap_abs_start_end_bounds(&mut start, &mut end);

        assert_eq!(
            start,
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive).to_start_bound()
        );
        assert_eq!(end, AbsEndBound::InfiniteFuture);
    }

    #[test]
    fn infinite_infinite() {
        let mut start = AbsStartBound::InfinitePast;
        let mut end = AbsEndBound::InfiniteFuture;

        swap_abs_start_end_bounds(&mut start, &mut end);

        assert_eq!(start, AbsStartBound::InfinitePast);
        assert_eq!(end, AbsEndBound::InfiniteFuture);
    }
}

mod check_abs_finite_start_end_bounds_for_interval_creation {
    use super::*;

    #[test]
    fn ok() {
        assert_eq!(
            check_abs_finite_start_end_bounds_for_interval_creation(
                &AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound(),
                &AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_end_bound(),
            ),
            Ok(()),
        );
    }

    #[test]
    fn wrong_order() {
        assert_eq!(
            check_abs_finite_start_end_bounds_for_interval_creation(
                &AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_start_bound(),
                &AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound(),
            ),
            Err(AbsStartEndBoundsCheckForIntervalCreationError::StartPastEnd),
        );
    }

    mod same_position {
        use super::*;

        #[test]
        fn inclusive_inclusive() {
            assert_eq!(
                check_abs_finite_start_end_bounds_for_interval_creation(
                    &AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound(),
                    &AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound(),
                ),
                Ok(()),
            );
        }

        #[test]
        fn inclusive_exclusive() {
            assert_eq!(
                check_abs_finite_start_end_bounds_for_interval_creation(
                    &AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound(),
                    &AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_finite_end_bound(),
                ),
                Err(AbsStartEndBoundsCheckForIntervalCreationError::SameTimeButNotDoublyInclusive),
            );
        }

        #[test]
        fn exclusive_inclusive() {
            assert_eq!(
                check_abs_finite_start_end_bounds_for_interval_creation(
                    &AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_finite_start_bound(),
                    &AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound(),
                ),
                Err(AbsStartEndBoundsCheckForIntervalCreationError::SameTimeButNotDoublyInclusive),
            );
        }

        #[test]
        fn exclusive_exclusive() {
            assert_eq!(
                check_abs_finite_start_end_bounds_for_interval_creation(
                    &AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_finite_start_bound(),
                    &AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_finite_end_bound(),
                ),
                Err(AbsStartEndBoundsCheckForIntervalCreationError::SameTimeButNotDoublyInclusive),
            );
        }
    }
}

mod check_abs_start_end_bounds_for_interval_creation {
    use super::*;

    mod finite_finite {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                check_abs_start_end_bounds_for_interval_creation(
                    &AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    &AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                ),
                Ok(()),
            );
        }

        #[test]
        fn wrong_order() {
            assert_eq!(
                check_abs_start_end_bounds_for_interval_creation(
                    &AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                    &AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
                ),
                Err(AbsStartEndBoundsCheckForIntervalCreationError::StartPastEnd),
            );
        }

        mod same_position {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                assert_eq!(
                    check_abs_start_end_bounds_for_interval_creation(
                        &AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                        &AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
                    ),
                    Ok(()),
                );
            }

            #[test]
            fn inclusive_exclusive() {
                assert_eq!(
                    check_abs_start_end_bounds_for_interval_creation(
                        &AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                        &AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                            .to_end_bound(),
                    ),
                    Err(AbsStartEndBoundsCheckForIntervalCreationError::SameTimeButNotDoublyInclusive),
                );
            }

            #[test]
            fn exclusive_inclusive() {
                assert_eq!(
                    check_abs_start_end_bounds_for_interval_creation(
                        &AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                            .to_start_bound(),
                        &AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
                    ),
                    Err(AbsStartEndBoundsCheckForIntervalCreationError::SameTimeButNotDoublyInclusive),
                );
            }

            #[test]
            fn exclusive_exclusive() {
                assert_eq!(
                    check_abs_start_end_bounds_for_interval_creation(
                        &AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                            .to_start_bound(),
                        &AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                            .to_end_bound(),
                    ),
                    Err(AbsStartEndBoundsCheckForIntervalCreationError::SameTimeButNotDoublyInclusive),
                );
            }
        }
    }

    #[test]
    fn finite_infinite() {
        assert_eq!(
            check_abs_start_end_bounds_for_interval_creation(
                &AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                &AbsEndBound::InfiniteFuture,
            ),
            Ok(()),
        );
    }

    #[test]
    fn infinite_finite() {
        assert_eq!(
            check_abs_start_end_bounds_for_interval_creation(
                &AbsStartBound::InfinitePast,
                &AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
            ),
            Ok(()),
        );
    }

    #[test]
    fn infinite_infinite() {
        assert_eq!(
            check_abs_start_end_bounds_for_interval_creation(
                &AbsStartBound::InfinitePast,
                &AbsEndBound::InfiniteFuture,
            ),
            Ok(()),
        );
    }
}

mod prepare_abs_finite_start_end_bounds_for_interval_creation {
    use super::*;

    #[test]
    fn ok() {
        let mut start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
        let mut end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_end_bound();

        let has_changed = prepare_abs_finite_start_end_bounds_for_interval_creation(&mut start, &mut end);

        assert!(!has_changed);
        assert_eq!(
            start,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound()
        );
        assert_eq!(
            end,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_end_bound()
        );
    }

    #[test]
    fn wrong_order() {
        let mut start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_start_bound();
        let mut end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound();

        let has_changed = prepare_abs_finite_start_end_bounds_for_interval_creation(&mut start, &mut end);

        assert!(has_changed);
        assert_eq!(
            start,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound()
        );
        assert_eq!(
            end,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_end_bound()
        );
    }

    mod same_position {
        use super::*;

        #[test]
        fn inclusive_inclusive() {
            let mut start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
            let mut end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound();

            let has_changed = prepare_abs_finite_start_end_bounds_for_interval_creation(&mut start, &mut end);

            assert!(!has_changed);
            assert_eq!(
                start,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound()
            );
            assert_eq!(
                end,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound()
            );
        }

        #[test]
        fn inclusive_exclusive() {
            let mut start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
            let mut end = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                .to_finite_end_bound();

            let has_changed = prepare_abs_finite_start_end_bounds_for_interval_creation(&mut start, &mut end);

            assert!(has_changed);
            assert_eq!(
                start,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound()
            );
            assert_eq!(
                end,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound()
            );
        }

        #[test]
        fn exclusive_inclusive() {
            let mut start = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                .to_finite_start_bound();
            let mut end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound();

            let has_changed = prepare_abs_finite_start_end_bounds_for_interval_creation(&mut start, &mut end);

            assert!(has_changed);
            assert_eq!(
                start,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound()
            );
            assert_eq!(
                end,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound()
            );
        }

        #[test]
        fn exclusive_exclusive() {
            let mut start = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                .to_finite_start_bound();
            let mut end = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                .to_finite_end_bound();

            let has_changed = prepare_abs_finite_start_end_bounds_for_interval_creation(&mut start, &mut end);

            assert!(has_changed);
            assert_eq!(
                start,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound()
            );
            assert_eq!(
                end,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound()
            );
        }
    }
}

mod prepare_abs_start_end_bounds_for_interval_creation {
    use super::*;

    mod finite_finite {
        use super::*;

        #[test]
        fn ok() {
            let mut start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound();
            let mut end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound();

            let has_changed = prepare_abs_start_end_bounds_for_interval_creation(&mut start, &mut end);

            assert!(!has_changed);
            assert_eq!(
                start,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound()
            );
            assert_eq!(end, AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound());
        }

        #[test]
        fn wrong_order() {
            let mut start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound();
            let mut end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound();

            let has_changed = prepare_abs_start_end_bounds_for_interval_creation(&mut start, &mut end);

            assert!(has_changed);
            assert_eq!(
                start,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound()
            );
            assert_eq!(end, AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound());
        }

        mod same_position {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let mut start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound();
                let mut end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound();

                let has_changed = prepare_abs_start_end_bounds_for_interval_creation(&mut start, &mut end);

                assert!(!has_changed);
                assert_eq!(
                    start,
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound()
                );
                assert_eq!(end, AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound());
            }

            #[test]
            fn inclusive_exclusive() {
                let mut start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound();
                let mut end = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                    .to_end_bound();

                let has_changed = prepare_abs_start_end_bounds_for_interval_creation(&mut start, &mut end);

                assert!(has_changed);
                assert_eq!(
                    start,
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound()
                );
                assert_eq!(end, AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound());
            }

            #[test]
            fn exclusive_inclusive() {
                let mut start =
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound();
                let mut end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound();

                let has_changed = prepare_abs_start_end_bounds_for_interval_creation(&mut start, &mut end);

                assert!(has_changed);
                assert_eq!(
                    start,
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound()
                );
                assert_eq!(end, AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound());
            }

            #[test]
            fn exclusive_exclusive() {
                let mut start =
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound();
                let mut end = AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                    .to_end_bound();

                let has_changed = prepare_abs_start_end_bounds_for_interval_creation(&mut start, &mut end);

                assert!(has_changed);
                assert_eq!(
                    start,
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound()
                );
                assert_eq!(end, AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound());
            }
        }
    }

    #[test]
    fn finite_infinite() {
        let mut start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound();
        let mut end = AbsEndBound::InfiniteFuture;

        let has_changed = prepare_abs_start_end_bounds_for_interval_creation(&mut start, &mut end);

        assert!(!has_changed);
        assert_eq!(
            start,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound()
        );
        assert_eq!(end, AbsEndBound::InfiniteFuture);
    }

    #[test]
    fn infinite_finite() {
        let mut start = AbsStartBound::InfinitePast;
        let mut end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound();

        let has_changed = prepare_abs_start_end_bounds_for_interval_creation(&mut start, &mut end);

        assert!(!has_changed);
        assert_eq!(start, AbsStartBound::InfinitePast);
        assert_eq!(end, AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound());
    }

    #[test]
    fn infinite_infinite() {
        let mut start = AbsStartBound::InfinitePast;
        let mut end = AbsEndBound::InfiniteFuture;

        let has_changed = prepare_abs_start_end_bounds_for_interval_creation(&mut start, &mut end);

        assert!(!has_changed);
        assert_eq!(start, AbsStartBound::InfinitePast);
        assert_eq!(end, AbsEndBound::InfiniteFuture);
    }
}
