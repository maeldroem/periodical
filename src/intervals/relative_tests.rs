use jiff::SignedDuration;

use super::relative::*;
use crate::intervals::meta::BoundInclusivity;

mod swap_rel_finite_start_end_bounds {
    use super::*;

    #[test]
    fn ok() {
        let mut start = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_finite_start_bound();
        let mut end = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Inclusive)
            .to_finite_end_bound();

        swap_rel_finite_start_end_bounds(&mut start, &mut end);

        assert_eq!(
            start,
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Inclusive)
                .to_finite_start_bound()
        );
        assert_eq!(
            end,
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                .to_finite_end_bound()
        );
    }
}

mod swap_rel_start_end_bounds {
    use super::*;

    #[test]
    fn finite_finite() {
        let mut start = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_start_bound();
        let mut end =
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Inclusive).to_end_bound();

        swap_rel_start_end_bounds(&mut start, &mut end);

        assert_eq!(
            start,
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Inclusive)
                .to_start_bound()
        );
        assert_eq!(
            end,
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive).to_end_bound()
        );
    }

    #[test]
    fn finite_infinite() {
        let mut start = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
            .to_start_bound();
        let mut end = RelEndBound::InfiniteFuture;

        swap_rel_start_end_bounds(&mut start, &mut end);

        assert_eq!(start, RelStartBound::InfinitePast);
        assert_eq!(
            end,
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive).to_end_bound()
        );
    }

    #[test]
    fn infinite_finite() {
        let mut start = RelStartBound::InfinitePast;
        let mut end =
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive).to_end_bound();

        swap_rel_start_end_bounds(&mut start, &mut end);

        assert_eq!(
            start,
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                .to_start_bound()
        );
        assert_eq!(end, RelEndBound::InfiniteFuture);
    }

    #[test]
    fn infinite_infinite() {
        let mut start = RelStartBound::InfinitePast;
        let mut end = RelEndBound::InfiniteFuture;

        swap_rel_start_end_bounds(&mut start, &mut end);

        assert_eq!(start, RelStartBound::InfinitePast);
        assert_eq!(end, RelEndBound::InfiniteFuture);
    }
}

mod check_rel_finite_start_end_bounds_for_interval_creation {
    use super::*;

    #[test]
    fn ok() {
        assert_eq!(
            check_rel_finite_start_end_bounds_for_interval_creation(
                &RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound(),
                &RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_end_bound(),
            ),
            Ok(()),
        );
    }

    #[test]
    fn wrong_order() {
        assert_eq!(
            check_rel_finite_start_end_bounds_for_interval_creation(
                &RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_start_bound(),
                &RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound(),
            ),
            Err(RelStartEndBoundsCheckForIntervalCreationError::StartPastEnd),
        );
    }

    mod same_position {
        use super::*;

        #[test]
        fn inclusive_inclusive() {
            assert_eq!(
                check_rel_finite_start_end_bounds_for_interval_creation(
                    &RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound(),
                    &RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound(),
                ),
                Ok(()),
            );
        }

        #[test]
        fn inclusive_exclusive() {
            assert_eq!(
                check_rel_finite_start_end_bounds_for_interval_creation(
                    &RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound(),
                    &RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_finite_end_bound(),
                ),
                Err(RelStartEndBoundsCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive),
            );
        }

        #[test]
        fn exclusive_inclusive() {
            assert_eq!(
                check_rel_finite_start_end_bounds_for_interval_creation(
                    &RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_finite_start_bound(),
                    &RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound(),
                ),
                Err(RelStartEndBoundsCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive),
            );
        }

        #[test]
        fn exclusive_exclusive() {
            assert_eq!(
                check_rel_finite_start_end_bounds_for_interval_creation(
                    &RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_finite_start_bound(),
                    &RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_finite_end_bound(),
                ),
                Err(RelStartEndBoundsCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive),
            );
        }
    }
}

mod check_rel_start_end_bounds_for_interval_creation {
    use super::*;

    mod finite_finite {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                check_rel_start_end_bounds_for_interval_creation(
                    &RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    &RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                Ok(()),
            );
        }

        #[test]
        fn wrong_order() {
            assert_eq!(
                check_rel_start_end_bounds_for_interval_creation(
                    &RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    &RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
                Err(RelStartEndBoundsCheckForIntervalCreationError::StartPastEnd),
            );
        }

        mod same_position {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                assert_eq!(
                    check_rel_start_end_bounds_for_interval_creation(
                        &RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                        &RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                    ),
                    Ok(()),
                );
            }

            #[test]
            fn inclusive_exclusive() {
                assert_eq!(
                    check_rel_start_end_bounds_for_interval_creation(
                        &RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                        &RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                            .to_end_bound(),
                    ),
                    Err(RelStartEndBoundsCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive),
                );
            }

            #[test]
            fn exclusive_inclusive() {
                assert_eq!(
                    check_rel_start_end_bounds_for_interval_creation(
                        &RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                            .to_start_bound(),
                        &RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                    ),
                    Err(RelStartEndBoundsCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive),
                );
            }

            #[test]
            fn exclusive_exclusive() {
                assert_eq!(
                    check_rel_start_end_bounds_for_interval_creation(
                        &RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                            .to_start_bound(),
                        &RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                            .to_end_bound(),
                    ),
                    Err(RelStartEndBoundsCheckForIntervalCreationError::SameOffsetButNotDoublyInclusive),
                );
            }
        }
    }

    #[test]
    fn finite_infinite() {
        assert_eq!(
            check_rel_start_end_bounds_for_interval_creation(
                &RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                &RelEndBound::InfiniteFuture,
            ),
            Ok(()),
        );
    }

    #[test]
    fn infinite_finite() {
        assert_eq!(
            check_rel_start_end_bounds_for_interval_creation(
                &RelStartBound::InfinitePast,
                &RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
            ),
            Ok(()),
        );
    }

    #[test]
    fn infinite_infinite() {
        assert_eq!(
            check_rel_start_end_bounds_for_interval_creation(
                &RelStartBound::InfinitePast,
                &RelEndBound::InfiniteFuture,
            ),
            Ok(()),
        );
    }
}

mod prepare_rel_finite_start_end_bounds_for_interval_creation {
    use super::*;

    #[test]
    fn ok() {
        let mut start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
        let mut end = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_end_bound();

        let has_changed = prepare_rel_finite_start_end_bounds_for_interval_creation(&mut start, &mut end);

        assert!(!has_changed);
        assert_eq!(
            start,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound()
        );
        assert_eq!(
            end,
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_end_bound()
        );
    }

    #[test]
    fn wrong_order() {
        let mut start = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_start_bound();
        let mut end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound();

        let has_changed = prepare_rel_finite_start_end_bounds_for_interval_creation(&mut start, &mut end);

        assert!(has_changed);
        assert_eq!(
            start,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound()
        );
        assert_eq!(
            end,
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_end_bound()
        );
    }

    mod same_position {
        use super::*;

        #[test]
        fn inclusive_inclusive() {
            let mut start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
            let mut end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound();

            let has_changed = prepare_rel_finite_start_end_bounds_for_interval_creation(&mut start, &mut end);

            assert!(!has_changed);
            assert_eq!(
                start,
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound()
            );
            assert_eq!(
                end,
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound()
            );
        }

        #[test]
        fn inclusive_exclusive() {
            let mut start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
            let mut end = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                .to_finite_end_bound();

            let has_changed = prepare_rel_finite_start_end_bounds_for_interval_creation(&mut start, &mut end);

            assert!(has_changed);
            assert_eq!(
                start,
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound()
            );
            assert_eq!(
                end,
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound()
            );
        }

        #[test]
        fn exclusive_inclusive() {
            let mut start =
                RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                    .to_finite_start_bound();
            let mut end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound();

            let has_changed = prepare_rel_finite_start_end_bounds_for_interval_creation(&mut start, &mut end);

            assert!(has_changed);
            assert_eq!(
                start,
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound()
            );
            assert_eq!(
                end,
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound()
            );
        }

        #[test]
        fn exclusive_exclusive() {
            let mut start =
                RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                    .to_finite_start_bound();
            let mut end = RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                .to_finite_end_bound();

            let has_changed = prepare_rel_finite_start_end_bounds_for_interval_creation(&mut start, &mut end);

            assert!(has_changed);
            assert_eq!(
                start,
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound()
            );
            assert_eq!(
                end,
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound()
            );
        }
    }
}

mod prepare_rel_start_end_bounds_for_interval_creation {
    use super::*;

    mod finite_finite {
        use super::*;

        #[test]
        fn ok() {
            let mut start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound();
            let mut end = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound();

            let has_changed = prepare_rel_start_end_bounds_for_interval_creation(&mut start, &mut end);

            assert!(!has_changed);
            assert_eq!(
                start,
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound()
            );
            assert_eq!(
                end,
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound()
            );
        }

        #[test]
        fn wrong_order() {
            let mut start = RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound();
            let mut end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound();

            let has_changed = prepare_rel_start_end_bounds_for_interval_creation(&mut start, &mut end);

            assert!(has_changed);
            assert_eq!(
                start,
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound()
            );
            assert_eq!(
                end,
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound()
            );
        }

        mod same_position {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let mut start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound();
                let mut end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound();

                let has_changed = prepare_rel_start_end_bounds_for_interval_creation(&mut start, &mut end);

                assert!(!has_changed);
                assert_eq!(
                    start,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound()
                );
                assert_eq!(
                    end,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let mut start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound();
                let mut end =
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_end_bound();

                let has_changed = prepare_rel_start_end_bounds_for_interval_creation(&mut start, &mut end);

                assert!(has_changed);
                assert_eq!(
                    start,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound()
                );
                assert_eq!(
                    end,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let mut start =
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound();
                let mut end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound();

                let has_changed = prepare_rel_start_end_bounds_for_interval_creation(&mut start, &mut end);

                assert!(has_changed);
                assert_eq!(
                    start,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound()
                );
                assert_eq!(
                    end,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let mut start =
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound();
                let mut end =
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_end_bound();

                let has_changed = prepare_rel_start_end_bounds_for_interval_creation(&mut start, &mut end);

                assert!(has_changed);
                assert_eq!(
                    start,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound()
                );
                assert_eq!(
                    end,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound()
                );
            }
        }
    }

    #[test]
    fn finite_infinite() {
        let mut start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound();
        let mut end = RelEndBound::InfiniteFuture;

        let has_changed = prepare_rel_start_end_bounds_for_interval_creation(&mut start, &mut end);

        assert!(!has_changed);
        assert_eq!(
            start,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound()
        );
        assert_eq!(end, RelEndBound::InfiniteFuture);
    }

    #[test]
    fn infinite_finite() {
        let mut start = RelStartBound::InfinitePast;
        let mut end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound();

        let has_changed = prepare_rel_start_end_bounds_for_interval_creation(&mut start, &mut end);

        assert!(!has_changed);
        assert_eq!(start, RelStartBound::InfinitePast);
        assert_eq!(
            end,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound()
        );
    }

    #[test]
    fn infinite_infinite() {
        let mut start = RelStartBound::InfinitePast;
        let mut end = RelEndBound::InfiniteFuture;

        let has_changed = prepare_rel_start_end_bounds_for_interval_creation(&mut start, &mut end);

        assert!(!has_changed);
        assert_eq!(start, RelStartBound::InfinitePast);
        assert_eq!(end, RelEndBound::InfiniteFuture);
    }
}
