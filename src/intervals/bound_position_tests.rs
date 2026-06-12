use std::error::Error;

use jiff::{SignedDuration, Timestamp};

use super::bound_position::*;
use crate::intervals::absolute::{AbsBoundPair, AbsEndBound, AbsFiniteBoundPos, AbsStartBound};
use crate::intervals::relative::{RelBoundPair, RelEndBound, RelFiniteBoundPos, RelStartBound};

#[test]
fn default_bound_position() {
    assert_eq!(BoundPosition::default(), BoundPosition::MIN);
}

mod index {
    use super::*;

    #[test]
    fn start() {
        assert_eq!(BoundPosition::Start(51907).index(), 51907);
    }

    #[test]
    fn end() {
        assert_eq!(BoundPosition::End(8976).index(), 8976);
    }
}

mod get_abs_bound {
    use super::*;

    #[test]
    fn start_inside() -> Result<(), Box<dyn Error>> {
        let data = [
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-02-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsFiniteBoundPos::new("2025-02-05 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-05-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsFiniteBoundPos::new("2025-05-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            ),
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture),
        ];

        assert_eq!(
            BoundPosition::Start(2).get_abs_bound(data.iter()),
            Some(
                AbsFiniteBoundPos::new("2025-05-01 00:00:00Z".parse::<Timestamp>()?)
                    .to_start_bound()
                    .to_bound()
            ),
        );
        Ok(())
    }

    #[test]
    fn start_outside() -> Result<(), Box<dyn Error>> {
        let data = [
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-02-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsFiniteBoundPos::new("2025-02-05 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-05-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsFiniteBoundPos::new("2025-05-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            ),
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture),
        ];

        assert_eq!(BoundPosition::Start(5).get_abs_bound(data.iter()), None);
        Ok(())
    }

    #[test]
    fn end_inside() -> Result<(), Box<dyn Error>> {
        let data = [
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-02-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsFiniteBoundPos::new("2025-02-05 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-05-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsFiniteBoundPos::new("2025-05-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            ),
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture),
        ];

        assert_eq!(
            BoundPosition::End(2).get_abs_bound(data.iter()),
            Some(
                AbsFiniteBoundPos::new("2025-05-04 00:00:00Z".parse::<Timestamp>()?)
                    .to_end_bound()
                    .to_bound()
            ),
        );
        Ok(())
    }

    #[test]
    fn end_outside() -> Result<(), Box<dyn Error>> {
        let data = [
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-02-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsFiniteBoundPos::new("2025-02-05 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-05-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsFiniteBoundPos::new("2025-05-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            ),
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture),
        ];

        assert_eq!(BoundPosition::End(5).get_abs_bound(data.iter()), None);
        Ok(())
    }
}

mod get_rel_bound {
    use super::*;

    #[test]
    fn start_inside() {
        let data = [
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(21)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(25)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(11)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(51)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(54)).to_end_bound(),
            ),
            RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture),
        ];

        assert_eq!(
            BoundPosition::Start(2).get_rel_bound(data.iter()),
            Some(
                RelFiniteBoundPos::new(SignedDuration::from_hours(51))
                    .to_start_bound()
                    .to_bound()
            ),
        );
    }

    #[test]
    fn start_outside() {
        let data = [
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(21)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(25)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(11)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(51)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(54)).to_end_bound(),
            ),
            RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture),
        ];

        assert_eq!(BoundPosition::Start(5).get_rel_bound(data.iter()), None);
    }

    #[test]
    fn end_inside() {
        let data = [
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(21)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(25)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(11)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(51)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(54)).to_end_bound(),
            ),
            RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture),
        ];

        assert_eq!(
            BoundPosition::End(2).get_rel_bound(data.iter()),
            Some(
                RelFiniteBoundPos::new(SignedDuration::from_hours(54))
                    .to_end_bound()
                    .to_bound()
            ),
        );
    }

    #[test]
    fn end_outside() {
        let data = [
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(21)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(25)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(11)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(51)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(54)).to_end_bound(),
            ),
            RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture),
        ];

        assert_eq!(BoundPosition::End(5).get_rel_bound(data.iter()), None);
    }
}

mod add_interval_index {
    use super::*;

    #[test]
    fn start_no_overflow() {
        let mut position = BoundPosition::Start(5);

        assert!(!position.add_interval_index(3));
        assert_eq!(position, BoundPosition::Start(8));
    }

    #[test]
    fn start_overflow() {
        let mut position = BoundPosition::Start(5);

        assert!(position.add_interval_index(usize::MAX));
        assert_eq!(position, BoundPosition::MAX);
    }

    #[test]
    fn end_no_overflow() {
        let mut position = BoundPosition::End(5);

        assert!(!position.add_interval_index(3));
        assert_eq!(position, BoundPosition::End(8));
    }

    #[test]
    fn end_overflow() {
        let mut position = BoundPosition::End(5);

        assert!(position.add_interval_index(usize::MAX));
        assert_eq!(position, BoundPosition::MAX);
    }
}

mod sub_interval_index {
    use super::*;

    #[test]
    fn start_no_underflow() {
        let mut position = BoundPosition::Start(8);

        assert!(!position.sub_interval_index(3));
        assert_eq!(position, BoundPosition::Start(5));
    }

    #[test]
    fn start_underflow() {
        let mut position = BoundPosition::Start(8);

        assert!(position.sub_interval_index(9));
        assert_eq!(position, BoundPosition::MIN);
    }

    #[test]
    fn end_no_underflow() {
        let mut position = BoundPosition::End(8);

        assert!(!position.sub_interval_index(3));
        assert_eq!(position, BoundPosition::End(5));
    }

    #[test]
    fn end_underflow() {
        let mut position = BoundPosition::End(8);

        assert!(position.sub_interval_index(9));
        assert_eq!(position, BoundPosition::MIN);
    }
}

mod increment_interval_index {
    use super::*;

    #[test]
    fn start_no_overflow() {
        let mut position = BoundPosition::Start(8);

        assert!(!position.increment_interval_index());
        assert_eq!(position, BoundPosition::Start(9));
    }

    #[test]
    fn start_overflow() {
        let mut position = BoundPosition::Start(usize::MAX);

        assert!(position.increment_interval_index());
        assert_eq!(position, BoundPosition::MAX);
    }

    #[test]
    fn end_no_overflow() {
        let mut position = BoundPosition::End(8);

        assert!(!position.increment_interval_index());
        assert_eq!(position, BoundPosition::End(9));
    }

    #[test]
    fn end_overflow() {
        let mut position = BoundPosition::End(usize::MAX);

        assert!(position.increment_interval_index());
        assert_eq!(position, BoundPosition::MAX);
    }
}

mod decrement_interval_index {
    use super::*;

    #[test]
    fn start_no_underflow() {
        let mut position = BoundPosition::Start(6);

        assert!(!position.decrement_interval_index());
        assert_eq!(position, BoundPosition::Start(5));
    }

    #[test]
    fn start_underflow() {
        let mut position = BoundPosition::Start(usize::MIN);

        assert!(position.decrement_interval_index());
        assert_eq!(position, BoundPosition::MIN);
    }

    #[test]
    fn end_no_underflow() {
        let mut position = BoundPosition::End(6);

        assert!(!position.decrement_interval_index());
        assert_eq!(position, BoundPosition::End(5));
    }

    #[test]
    fn end_underflow() {
        let mut position = BoundPosition::End(usize::MIN);

        assert!(position.decrement_interval_index());
        assert_eq!(position, BoundPosition::MIN);
    }
}

mod advance_by {
    use super::*;

    mod even_count {
        use super::*;

        #[test]
        fn start_no_overflow() {
            let mut position = BoundPosition::Start(5);

            assert!(!position.advance_by(8));
            assert_eq!(position, BoundPosition::Start(9));
        }

        #[test]
        fn start_overflow() {
            let mut position = BoundPosition::Start(5);

            assert!(!position.advance_by(usize::MAX - 1));
            assert!(position.advance_by(usize::MAX - 1));
            assert_eq!(position, BoundPosition::MAX);
        }

        #[test]
        fn end_no_overflow() {
            let mut position = BoundPosition::End(5);

            assert!(!position.advance_by(8));
            assert_eq!(position, BoundPosition::End(9));
        }

        #[test]
        fn end_overflow() {
            let mut position = BoundPosition::End(5);

            assert!(!position.advance_by(usize::MAX - 1));
            assert!(position.advance_by(usize::MAX - 1));
            assert_eq!(position, BoundPosition::MAX);
        }
    }

    mod odd_count {
        use super::*;

        #[test]
        fn start_no_overflow() {
            let mut position = BoundPosition::Start(5);

            assert!(!position.advance_by(7));
            assert_eq!(position, BoundPosition::End(8));
        }

        #[test]
        fn start_overflow() {
            let mut position = BoundPosition::Start(5);

            assert!(!position.advance_by(usize::MAX));
            assert!(position.advance_by(usize::MAX));
            assert_eq!(position, BoundPosition::MAX);
        }

        #[test]
        fn end_no_overflow() {
            let mut position = BoundPosition::End(5);

            assert!(!position.advance_by(7));
            assert_eq!(position, BoundPosition::Start(9));
        }

        #[test]
        fn end_overflow() {
            let mut position = BoundPosition::End(5);

            assert!(!position.advance_by(usize::MAX));
            assert!(position.advance_by(usize::MAX));
            assert_eq!(position, BoundPosition::MAX);
        }
    }
}

mod advance_back_by {
    use super::*;

    mod even_count {
        use super::*;

        #[test]
        fn start_no_underflow() {
            let mut position = BoundPosition::Start(10);

            assert!(!position.advance_back_by(8));
            assert_eq!(position, BoundPosition::Start(6));
        }

        #[test]
        fn start_underflow() {
            let mut position = BoundPosition::Start(10);

            assert!(position.advance_back_by(30));
            assert_eq!(position, BoundPosition::MIN);
        }

        #[test]
        fn end_no_underflow() {
            let mut position = BoundPosition::End(10);

            assert!(!position.advance_back_by(8));
            assert_eq!(position, BoundPosition::End(6));
        }

        #[test]
        fn end_underflow() {
            let mut position = BoundPosition::End(10);

            assert!(position.advance_back_by(30));
            assert_eq!(position, BoundPosition::MIN);
        }
    }

    mod odd_count {
        use super::*;

        #[test]
        fn start_no_underflow() {
            let mut position = BoundPosition::Start(10);

            assert!(!position.advance_back_by(7));
            assert_eq!(position, BoundPosition::End(6));
        }

        #[test]
        fn start_underflow() {
            let mut position = BoundPosition::Start(10);

            assert!(position.advance_back_by(23));
            assert_eq!(position, BoundPosition::MIN);
        }

        #[test]
        fn end_no_underflow() {
            let mut position = BoundPosition::End(10);

            assert!(!position.advance_back_by(7));
            assert_eq!(position, BoundPosition::Start(7));
        }

        #[test]
        fn end_underflow() {
            let mut position = BoundPosition::End(10);

            assert!(position.advance_back_by(23));
            assert_eq!(position, BoundPosition::MIN);
        }
    }
}

mod next_bound {
    use super::*;

    mod start {
        use super::*;

        #[test]
        fn no_overflow() {
            let mut position = BoundPosition::Start(5);

            assert!(!position.next_bound());
            assert_eq!(position, BoundPosition::End(5));
        }

        #[test]
        fn overflow() {
            let mut position = BoundPosition::Start(usize::MAX);

            assert!(!position.next_bound());
            assert_eq!(position, BoundPosition::End(usize::MAX));
        }
    }

    mod end {
        use super::*;

        #[test]
        fn no_overflow() {
            let mut position = BoundPosition::End(5);

            assert!(!position.next_bound());
            assert_eq!(position, BoundPosition::Start(6));
        }

        #[test]
        fn overflow() {
            let mut position = BoundPosition::End(usize::MAX);

            assert!(position.next_bound());
            assert_eq!(position, BoundPosition::MAX);
        }
    }
}

mod prev_bound {
    use super::*;

    mod start {
        use super::*;

        #[test]
        fn no_underflow() {
            let mut position = BoundPosition::Start(5);

            assert!(!position.prev_bound());
            assert_eq!(position, BoundPosition::End(4));
        }

        #[test]
        fn underflow() {
            let mut position = BoundPosition::Start(usize::MIN);

            assert!(position.prev_bound());
            assert_eq!(position, BoundPosition::MIN);
        }
    }

    mod end {
        use super::*;

        #[test]
        fn no_underflow() {
            let mut position = BoundPosition::End(5);

            assert!(!position.prev_bound());
            assert_eq!(position, BoundPosition::Start(5));
        }

        #[test]
        fn underflow() {
            let mut position = BoundPosition::End(usize::MIN);

            assert!(!position.prev_bound());
            assert_eq!(position, BoundPosition::Start(usize::MIN));
        }
    }
}
