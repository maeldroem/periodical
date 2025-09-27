use super::meta::*;

#[test]
fn opening_direction_from_bool() {
    assert_eq!(OpeningDirection::from(true), OpeningDirection::ToFuture);
    assert_eq!(OpeningDirection::from(false), OpeningDirection::ToPast);
}

#[test]
fn epsilon_has_epsilon() {
    assert!(!Epsilon::None.has_epsilon());
    assert!(Epsilon::Start.has_epsilon());
    assert!(Epsilon::End.has_epsilon());
    assert!(Epsilon::Both.has_epsilon());
}

#[test]
fn epsilon_has_epsilon_on_start() {
    assert!(!Epsilon::None.has_epsilon_on_start());
    assert!(Epsilon::Start.has_epsilon_on_start());
    assert!(!Epsilon::End.has_epsilon_on_start());
    assert!(Epsilon::Both.has_epsilon_on_start());
}

#[test]
fn epsilon_has_epsilon_on_end() {
    assert!(!Epsilon::None.has_epsilon_on_end());
    assert!(!Epsilon::Start.has_epsilon_on_end());
    assert!(Epsilon::End.has_epsilon_on_end());
    assert!(Epsilon::Both.has_epsilon_on_end());
}

#[test]
fn epsilon_interpret_as_duration_bound_specific_none() {
    assert_eq!(
        Epsilon::None.interpret_as_duration_bound_specific(chrono::Duration::seconds(1), chrono::Duration::seconds(2)),
        Ok(chrono::Duration::zero()),
    );
}

#[test]
fn epsilon_interpret_as_duration_bound_specific_start() {
    assert_eq!(
        Epsilon::Start.interpret_as_duration_bound_specific(chrono::Duration::seconds(1), chrono::Duration::seconds(2)),
        Ok(chrono::Duration::seconds(1)),
    );
}

#[test]
fn epsilon_interpret_as_duration_bound_specific_end() {
    assert_eq!(
        Epsilon::End.interpret_as_duration_bound_specific(chrono::Duration::seconds(1), chrono::Duration::seconds(2)),
        Ok(chrono::Duration::seconds(2)),
    );
}

#[test]
fn epsilon_interpret_as_duration_bound_specific_both() {
    assert_eq!(
        Epsilon::Both.interpret_as_duration_bound_specific(chrono::Duration::seconds(1), chrono::Duration::seconds(2)),
        Ok(chrono::Duration::seconds(3)),
    );
}

#[test]
fn epsilon_interpret_as_duration_none() {
    assert_eq!(
        Epsilon::None.interpret_as_duration(chrono::Duration::seconds(1)),
        Ok(chrono::Duration::zero())
    );
}

#[test]
fn epsilon_interpret_as_duration_start() {
    assert_eq!(
        Epsilon::Start.interpret_as_duration(chrono::Duration::seconds(1)),
        Ok(chrono::Duration::seconds(1))
    );
}

#[test]
fn epsilon_interpret_as_duration_end() {
    assert_eq!(
        Epsilon::End.interpret_as_duration(chrono::Duration::seconds(1)),
        Ok(chrono::Duration::seconds(1))
    );
}

#[test]
fn epsilon_interpret_as_duration_both() {
    assert_eq!(
        Epsilon::Both.interpret_as_duration(chrono::Duration::seconds(1)),
        Ok(chrono::Duration::seconds(2))
    );
}

#[test]
fn epsilon_from_bound_inclusivity_pair_inclusive_inclusive() {
    assert_eq!(
        Epsilon::from((BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)),
        Epsilon::None
    );
}

#[test]
fn epsilon_from_bound_inclusivity_pair_exclusive_inclusive() {
    assert_eq!(
        Epsilon::from((BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)),
        Epsilon::Start
    );
}

#[test]
fn epsilon_from_bound_inclusivity_pair_inclusive_exclusive() {
    assert_eq!(
        Epsilon::from((BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)),
        Epsilon::End
    );
}

#[test]
fn epsilon_from_bound_inclusivity_pair_exclusive_exclusive() {
    assert_eq!(
        Epsilon::from((BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)),
        Epsilon::Both
    );
}

#[test]
fn epsilon_from_bool_pair_false_false() {
    assert_eq!(Epsilon::from((false, false)), Epsilon::None);
}

#[test]
fn epsilon_from_bool_pair_true_false() {
    assert_eq!(Epsilon::from((true, false)), Epsilon::Start);
}

#[test]
fn epsilon_from_bool_pair_false_true() {
    assert_eq!(Epsilon::from((false, true)), Epsilon::End);
}

#[test]
fn epsilon_from_bool_pair_true_true() {
    assert_eq!(Epsilon::from((true, true)), Epsilon::Both);
}

#[test]
fn interval_duration_is_finite() {
    assert!(Duration::Finite(chrono::Duration::zero(), Epsilon::None).is_finite());
    assert!(!Duration::Infinite.is_finite());
}

#[test]
fn interval_duration_finite() {
    assert_eq!(
        Duration::Finite(chrono::Duration::hours(2), Epsilon::End).finite(),
        Some((chrono::Duration::hours(2), Epsilon::End)),
    );
    assert_eq!(Duration::Infinite.finite(), None);
}

#[test]
fn interval_duration_finite_interpret_duration_on_finite() {
    assert_eq!(
        Duration::Finite(chrono::Duration::hours(1), Epsilon::End)
            .finite_interpret_epsilon(chrono::Duration::seconds(1)),
        Some(chrono::Duration::minutes(59) + chrono::Duration::seconds(59)),
    );
}

#[test]
fn interval_duration_finite_interpret_duration_on_infinite() {
    assert_eq!(
        Duration::Infinite.finite_interpret_epsilon(chrono::Duration::seconds(1)),
        None,
    );
}

#[test]
fn interval_duration_finite_interpret_duration_on_finite_large_epsilon() {
    assert_eq!(
        Duration::Finite(chrono::Duration::hours(1), Epsilon::Start)
            .finite_interpret_epsilon(chrono::Duration::hours(2)),
        Some(chrono::Duration::zero()),
    );
}

#[test]
fn interval_duration_finite_strip_epsilon_finite() {
    assert_eq!(
        Duration::Finite(chrono::Duration::hours(2), Epsilon::Both).finite_strip_epsilon(),
        Some(chrono::Duration::hours(2)),
    );
}

#[test]
fn interval_duration_finite_strip_epsilon_infinite() {
    assert_eq!(Duration::Infinite.finite_strip_epsilon(), None);
}

#[test]
fn interval_duration_from_duration() {
    assert_eq!(
        Duration::from(chrono::Duration::zero()),
        Duration::Finite(chrono::Duration::zero(), Epsilon::default())
    );
}

#[test]
fn interval_duration_from_duration_and_epsilon() {
    assert_eq!(
        Duration::from((chrono::Duration::hours(2), Epsilon::End)),
        Duration::Finite(chrono::Duration::hours(2), Epsilon::End),
    );
}

#[test]
fn bound_inclusivity_default() {
    assert_eq!(BoundInclusivity::default(), BoundInclusivity::Inclusive);
}

#[test]
fn bound_inclusive_from_bool() {
    assert_eq!(BoundInclusivity::from(true), BoundInclusivity::Inclusive);
    assert_eq!(BoundInclusivity::from(false), BoundInclusivity::Exclusive);
}
