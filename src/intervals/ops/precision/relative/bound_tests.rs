use std::time::Duration;

use jiff::SignedDuration;

use super::bound::*;
use crate::intervals::relative::{RelEndBound, RelFiniteBoundPos, RelStartBound};
use crate::ops::{Precision, PrecisionMode, PrecisionOutOfRangeError};

mod finite_bound_pos {
    use super::*;

    mod precise {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                RelFiniteBoundPos::new(SignedDuration::from_mins(20)).precise(Precision::unchecked_new(
                    Duration::from_mins(15),
                    PrecisionMode::ToFuture
                ),),
                Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(30)))
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                RelFiniteBoundPos::new(SignedDuration::MAX).precise(Precision::unchecked_new(
                    Duration::from_mins(10),
                    PrecisionMode::ToFuture
                )),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod precise_with_base_offset {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                RelFiniteBoundPos::new(SignedDuration::from_mins(20)).precise_with_base_offset(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(10)
                ),
                Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(25)))
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                RelFiniteBoundPos::new(SignedDuration::MAX).precise_with_base_offset(
                    Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(10)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

mod finite_start_bound {
    use super::*;

    mod precise {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                RelFiniteBoundPos::new(SignedDuration::from_mins(20))
                    .to_finite_start_bound()
                    .precise(Precision::unchecked_new(
                        Duration::from_mins(15),
                        PrecisionMode::ToFuture
                    ),),
                Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(30)).to_finite_start_bound())
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                RelFiniteBoundPos::new(SignedDuration::MAX)
                    .to_finite_start_bound()
                    .precise(Precision::unchecked_new(
                        Duration::from_mins(10),
                        PrecisionMode::ToFuture
                    )),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod precise_with_base_offset {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                RelFiniteBoundPos::new(SignedDuration::from_mins(20))
                    .to_finite_start_bound()
                    .precise_with_base_offset(
                        Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                        SignedDuration::from_mins(10)
                    ),
                Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(25)).to_finite_start_bound())
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                RelFiniteBoundPos::new(SignedDuration::MAX)
                    .to_finite_start_bound()
                    .precise_with_base_offset(
                        Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                        SignedDuration::from_mins(10)
                    ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

mod finite_end_bound {
    use super::*;

    mod precise {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                RelFiniteBoundPos::new(SignedDuration::from_mins(20))
                    .to_finite_end_bound()
                    .precise(Precision::unchecked_new(
                        Duration::from_mins(15),
                        PrecisionMode::ToFuture
                    ),),
                Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(30)).to_finite_end_bound())
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                RelFiniteBoundPos::new(SignedDuration::MAX)
                    .to_finite_end_bound()
                    .precise(Precision::unchecked_new(
                        Duration::from_mins(10),
                        PrecisionMode::ToFuture
                    )),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod precise_with_base_offset {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                RelFiniteBoundPos::new(SignedDuration::from_mins(20))
                    .to_finite_end_bound()
                    .precise_with_base_offset(
                        Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                        SignedDuration::from_mins(10)
                    ),
                Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(25)).to_finite_end_bound())
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                RelFiniteBoundPos::new(SignedDuration::MAX)
                    .to_finite_end_bound()
                    .precise_with_base_offset(
                        Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                        SignedDuration::from_mins(10)
                    ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

mod finite_bound {
    use super::*;

    mod precise {
        use super::*;

        mod start {
            use super::*;

            #[test]
            fn ok() {
                assert_eq!(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20))
                        .to_finite_start_bound()
                        .to_finite_bound()
                        .precise(Precision::unchecked_new(
                            Duration::from_mins(15),
                            PrecisionMode::ToFuture
                        ),),
                    Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(30))
                        .to_finite_start_bound()
                        .to_finite_bound())
                );
            }

            #[test]
            fn precision_out_of_range_error() {
                assert_eq!(
                    RelFiniteBoundPos::new(SignedDuration::MAX)
                        .to_finite_start_bound()
                        .to_finite_bound()
                        .precise(Precision::unchecked_new(
                            Duration::from_mins(10),
                            PrecisionMode::ToFuture
                        )),
                    Err(PrecisionOutOfRangeError)
                );
            }
        }

        mod end {
            use super::*;

            #[test]
            fn ok() {
                assert_eq!(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20))
                        .to_finite_end_bound()
                        .to_finite_bound()
                        .precise(Precision::unchecked_new(
                            Duration::from_mins(15),
                            PrecisionMode::ToFuture
                        ),),
                    Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(30))
                        .to_finite_end_bound()
                        .to_finite_bound())
                );
            }

            #[test]
            fn precision_out_of_range_error() {
                assert_eq!(
                    RelFiniteBoundPos::new(SignedDuration::MAX)
                        .to_finite_end_bound()
                        .to_finite_bound()
                        .precise(Precision::unchecked_new(
                            Duration::from_mins(10),
                            PrecisionMode::ToFuture
                        )),
                    Err(PrecisionOutOfRangeError)
                );
            }
        }
    }

    mod precise_with_base_offset {
        use super::*;

        mod start {
            use super::*;

            #[test]
            fn ok() {
                assert_eq!(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20))
                        .to_finite_start_bound()
                        .to_finite_bound()
                        .precise_with_base_offset(
                            Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                            SignedDuration::from_mins(10)
                        ),
                    Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(25))
                        .to_finite_start_bound()
                        .to_finite_bound())
                );
            }

            #[test]
            fn precision_out_of_range_error() {
                assert_eq!(
                    RelFiniteBoundPos::new(SignedDuration::MAX)
                        .to_finite_start_bound()
                        .to_finite_bound()
                        .precise_with_base_offset(
                            Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                            SignedDuration::from_mins(10)
                        ),
                    Err(PrecisionOutOfRangeError)
                );
            }
        }

        mod end {
            use super::*;

            #[test]
            fn ok() {
                assert_eq!(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20))
                        .to_finite_end_bound()
                        .to_finite_bound()
                        .precise_with_base_offset(
                            Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                            SignedDuration::from_mins(10)
                        ),
                    Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(25))
                        .to_finite_end_bound()
                        .to_finite_bound())
                );
            }

            #[test]
            fn precision_out_of_range_error() {
                assert_eq!(
                    RelFiniteBoundPos::new(SignedDuration::MAX)
                        .to_finite_end_bound()
                        .to_finite_bound()
                        .precise_with_base_offset(
                            Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                            SignedDuration::from_mins(10)
                        ),
                    Err(PrecisionOutOfRangeError)
                );
            }
        }
    }
}

mod start_bound {
    use super::*;

    mod precise {
        use super::*;

        #[test]
        fn ok_finite() {
            assert_eq!(
                RelFiniteBoundPos::new(SignedDuration::from_mins(20))
                    .to_start_bound()
                    .precise(Precision::unchecked_new(
                        Duration::from_mins(15),
                        PrecisionMode::ToFuture
                    ),),
                Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(30)).to_start_bound())
            );
        }

        #[test]
        fn ok_infinite() {
            assert_eq!(
                RelStartBound::InfinitePast.precise(Precision::unchecked_new(
                    Duration::from_mins(15),
                    PrecisionMode::ToFuture
                ),),
                Ok(RelStartBound::InfinitePast)
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                RelFiniteBoundPos::new(SignedDuration::MAX)
                    .to_start_bound()
                    .precise(Precision::unchecked_new(
                        Duration::from_mins(10),
                        PrecisionMode::ToFuture
                    )),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod precise_with_base_offset {
        use super::*;

        #[test]
        fn ok_finite() {
            assert_eq!(
                RelFiniteBoundPos::new(SignedDuration::from_mins(20))
                    .to_start_bound()
                    .precise_with_base_offset(
                        Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                        SignedDuration::from_mins(10)
                    ),
                Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(25)).to_start_bound())
            );
        }

        #[test]
        fn ok_infinite() {
            assert_eq!(
                RelStartBound::InfinitePast.precise_with_base_offset(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(10)
                ),
                Ok(RelStartBound::InfinitePast)
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                RelFiniteBoundPos::new(SignedDuration::MAX)
                    .to_start_bound()
                    .precise_with_base_offset(
                        Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                        SignedDuration::from_mins(10)
                    ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

mod end_bound {
    use super::*;

    mod precise {
        use super::*;

        #[test]
        fn ok_finite() {
            assert_eq!(
                RelFiniteBoundPos::new(SignedDuration::from_mins(20))
                    .to_end_bound()
                    .precise(Precision::unchecked_new(
                        Duration::from_mins(15),
                        PrecisionMode::ToFuture
                    ),),
                Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(30)).to_end_bound())
            );
        }

        #[test]
        fn ok_infinite() {
            assert_eq!(
                RelEndBound::InfiniteFuture.precise(Precision::unchecked_new(
                    Duration::from_mins(15),
                    PrecisionMode::ToFuture
                ),),
                Ok(RelEndBound::InfiniteFuture)
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                RelFiniteBoundPos::new(SignedDuration::MAX)
                    .to_end_bound()
                    .precise(Precision::unchecked_new(
                        Duration::from_mins(10),
                        PrecisionMode::ToFuture
                    )),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod precise_with_base_offset {
        use super::*;

        #[test]
        fn ok_finite() {
            assert_eq!(
                RelFiniteBoundPos::new(SignedDuration::from_mins(20))
                    .to_end_bound()
                    .precise_with_base_offset(
                        Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                        SignedDuration::from_mins(10)
                    ),
                Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(25)).to_end_bound())
            );
        }

        #[test]
        fn ok_infinite() {
            assert_eq!(
                RelEndBound::InfiniteFuture.precise_with_base_offset(
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(10)
                ),
                Ok(RelEndBound::InfiniteFuture)
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                RelFiniteBoundPos::new(SignedDuration::MAX)
                    .to_end_bound()
                    .precise_with_base_offset(
                        Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                        SignedDuration::from_mins(10)
                    ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

mod bound {
    use super::*;

    mod precise {
        use super::*;

        mod start {
            use super::*;

            #[test]
            fn ok_finite() {
                assert_eq!(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20))
                        .to_start_bound()
                        .to_bound()
                        .precise(Precision::unchecked_new(
                            Duration::from_mins(15),
                            PrecisionMode::ToFuture
                        ),),
                    Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(30))
                        .to_start_bound()
                        .to_bound())
                );
            }

            #[test]
            fn ok_infinite() {
                assert_eq!(
                    RelStartBound::InfinitePast.to_bound().precise(Precision::unchecked_new(
                        Duration::from_mins(15),
                        PrecisionMode::ToFuture
                    ),),
                    Ok(RelStartBound::InfinitePast.to_bound())
                );
            }

            #[test]
            fn precision_out_of_range_error() {
                assert_eq!(
                    RelFiniteBoundPos::new(SignedDuration::MAX)
                        .to_start_bound()
                        .to_bound()
                        .precise(Precision::unchecked_new(
                            Duration::from_mins(10),
                            PrecisionMode::ToFuture
                        )),
                    Err(PrecisionOutOfRangeError)
                );
            }
        }

        mod end {
            use super::*;

            #[test]
            fn ok_finite() {
                assert_eq!(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20))
                        .to_end_bound()
                        .to_bound()
                        .precise(Precision::unchecked_new(
                            Duration::from_mins(15),
                            PrecisionMode::ToFuture
                        ),),
                    Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(30))
                        .to_end_bound()
                        .to_bound())
                );
            }

            #[test]
            fn ok_infinite() {
                assert_eq!(
                    RelEndBound::InfiniteFuture.to_bound().precise(Precision::unchecked_new(
                        Duration::from_mins(15),
                        PrecisionMode::ToFuture
                    ),),
                    Ok(RelEndBound::InfiniteFuture.to_bound())
                );
            }

            #[test]
            fn precision_out_of_range_error() {
                assert_eq!(
                    RelFiniteBoundPos::new(SignedDuration::MAX)
                        .to_end_bound()
                        .to_bound()
                        .precise(Precision::unchecked_new(
                            Duration::from_mins(10),
                            PrecisionMode::ToFuture
                        )),
                    Err(PrecisionOutOfRangeError)
                );
            }
        }
    }

    mod precise_with_base_offset {
        use super::*;

        mod start {
            use super::*;

            #[test]
            fn ok_finite() {
                assert_eq!(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20))
                        .to_start_bound()
                        .to_bound()
                        .precise_with_base_offset(
                            Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                            SignedDuration::from_mins(10)
                        ),
                    Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(25))
                        .to_start_bound()
                        .to_bound())
                );
            }

            #[test]
            fn ok_infinite() {
                assert_eq!(
                    RelStartBound::InfinitePast.to_bound().precise_with_base_offset(
                        Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                        SignedDuration::from_mins(10)
                    ),
                    Ok(RelStartBound::InfinitePast.to_bound())
                );
            }

            #[test]
            fn precision_out_of_range_error() {
                assert_eq!(
                    RelFiniteBoundPos::new(SignedDuration::MAX)
                        .to_start_bound()
                        .to_bound()
                        .precise_with_base_offset(
                            Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                            SignedDuration::from_mins(10)
                        ),
                    Err(PrecisionOutOfRangeError)
                );
            }
        }

        mod end {
            use super::*;

            #[test]
            fn ok_finite() {
                assert_eq!(
                    RelFiniteBoundPos::new(SignedDuration::from_mins(20))
                        .to_end_bound()
                        .to_bound()
                        .precise_with_base_offset(
                            Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                            SignedDuration::from_mins(10)
                        ),
                    Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(25))
                        .to_end_bound()
                        .to_bound())
                );
            }

            #[test]
            fn ok_infinite() {
                assert_eq!(
                    RelEndBound::InfiniteFuture.to_bound().precise_with_base_offset(
                        Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                        SignedDuration::from_mins(10)
                    ),
                    Ok(RelEndBound::InfiniteFuture.to_bound())
                );
            }

            #[test]
            fn precision_out_of_range_error() {
                assert_eq!(
                    RelFiniteBoundPos::new(SignedDuration::MAX)
                        .to_end_bound()
                        .to_bound()
                        .precise_with_base_offset(
                            Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                            SignedDuration::from_mins(10)
                        ),
                    Err(PrecisionOutOfRangeError)
                );
            }
        }
    }
}

mod precise_rel_finite_bound_pos {
    use super::*;

    #[test]
    fn ok() {
        assert_eq!(
            precise_rel_finite_bound_pos(
                &RelFiniteBoundPos::new(SignedDuration::from_mins(20)),
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
            ),
            Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(30)))
        );
    }

    #[test]
    fn precision_out_of_range_error() {
        assert_eq!(
            precise_rel_finite_bound_pos(
                &RelFiniteBoundPos::new(SignedDuration::MAX),
                Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

mod precise_rel_finite_bound_pos_with_base_offset {
    use super::*;

    #[test]
    fn ok() {
        assert_eq!(
            precise_rel_finite_bound_pos_with_base_offset(
                &RelFiniteBoundPos::new(SignedDuration::from_mins(20)),
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                SignedDuration::from_mins(10)
            ),
            Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(25)))
        );
    }

    #[test]
    fn precision_out_of_range_error() {
        assert_eq!(
            precise_rel_finite_bound_pos_with_base_offset(
                &RelFiniteBoundPos::new(SignedDuration::MAX),
                Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                SignedDuration::from_mins(10)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

mod precise_rel_finite_start_bound {
    use super::*;

    #[test]
    fn ok() {
        assert_eq!(
            precise_rel_finite_start_bound(
                &RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_finite_start_bound(),
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
            ),
            Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(30)).to_finite_start_bound())
        );
    }

    #[test]
    fn precision_out_of_range_error() {
        assert_eq!(
            precise_rel_finite_start_bound(
                &RelFiniteBoundPos::new(SignedDuration::MAX).to_finite_start_bound(),
                Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

mod precise_rel_finite_start_bound_with_base_offset {
    use super::*;

    #[test]
    fn ok() {
        assert_eq!(
            precise_rel_finite_start_bound_with_base_offset(
                &RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_finite_start_bound(),
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                SignedDuration::from_mins(10)
            ),
            Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(25)).to_finite_start_bound())
        );
    }

    #[test]
    fn precision_out_of_range_error() {
        assert_eq!(
            precise_rel_finite_start_bound_with_base_offset(
                &RelFiniteBoundPos::new(SignedDuration::MAX).to_finite_start_bound(),
                Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                SignedDuration::from_mins(10)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

mod precise_rel_finite_end_bound {
    use super::*;

    #[test]
    fn ok() {
        assert_eq!(
            precise_rel_finite_end_bound(
                &RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_finite_end_bound(),
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
            ),
            Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(30)).to_finite_end_bound())
        );
    }

    #[test]
    fn precision_out_of_range_error() {
        assert_eq!(
            precise_rel_finite_end_bound(
                &RelFiniteBoundPos::new(SignedDuration::MAX).to_finite_end_bound(),
                Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

mod precise_rel_finite_end_bound_with_base_offset {
    use super::*;

    #[test]
    fn ok() {
        assert_eq!(
            precise_rel_finite_end_bound_with_base_offset(
                &RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_finite_end_bound(),
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                SignedDuration::from_mins(10)
            ),
            Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(25)).to_finite_end_bound())
        );
    }

    #[test]
    fn precision_out_of_range_error() {
        assert_eq!(
            precise_rel_finite_end_bound_with_base_offset(
                &RelFiniteBoundPos::new(SignedDuration::MAX).to_finite_end_bound(),
                Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                SignedDuration::from_mins(10)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

mod precise_rel_finite_bound {
    use super::*;

    mod start {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                precise_rel_finite_bound(
                    &RelFiniteBoundPos::new(SignedDuration::from_mins(20))
                        .to_finite_start_bound()
                        .to_finite_bound(),
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                ),
                Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(30))
                    .to_finite_start_bound()
                    .to_finite_bound())
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                precise_rel_finite_bound(
                    &RelFiniteBoundPos::new(SignedDuration::MAX)
                        .to_finite_start_bound()
                        .to_finite_bound(),
                    Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod end {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                precise_rel_finite_bound(
                    &RelFiniteBoundPos::new(SignedDuration::from_mins(20))
                        .to_finite_end_bound()
                        .to_finite_bound(),
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                ),
                Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(30))
                    .to_finite_end_bound()
                    .to_finite_bound())
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                precise_rel_finite_bound(
                    &RelFiniteBoundPos::new(SignedDuration::MAX)
                        .to_finite_end_bound()
                        .to_finite_bound(),
                    Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

mod precise_rel_finite_bound_with_base_offset {
    use super::*;

    mod start {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                precise_rel_finite_bound_with_base_offset(
                    &RelFiniteBoundPos::new(SignedDuration::from_mins(20))
                        .to_finite_start_bound()
                        .to_finite_bound(),
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(10)
                ),
                Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(25))
                    .to_finite_start_bound()
                    .to_finite_bound())
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                precise_rel_finite_bound_with_base_offset(
                    &RelFiniteBoundPos::new(SignedDuration::MAX)
                        .to_finite_start_bound()
                        .to_finite_bound(),
                    Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(10)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod end {
        use super::*;

        #[test]
        fn ok() {
            assert_eq!(
                precise_rel_finite_bound_with_base_offset(
                    &RelFiniteBoundPos::new(SignedDuration::from_mins(20))
                        .to_finite_end_bound()
                        .to_finite_bound(),
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(10)
                ),
                Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(25))
                    .to_finite_end_bound()
                    .to_finite_bound())
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                precise_rel_finite_bound_with_base_offset(
                    &RelFiniteBoundPos::new(SignedDuration::MAX)
                        .to_finite_end_bound()
                        .to_finite_bound(),
                    Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(10)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

mod precise_rel_start_bound {
    use super::*;

    #[test]
    fn ok_finite() {
        assert_eq!(
            precise_rel_start_bound(
                &RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_start_bound(),
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
            ),
            Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(30)).to_start_bound())
        );
    }

    #[test]
    fn ok_infinite() {
        assert_eq!(
            precise_rel_start_bound(
                &RelStartBound::InfinitePast,
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
            ),
            Ok(RelStartBound::InfinitePast)
        );
    }

    #[test]
    fn precision_out_of_range_error() {
        assert_eq!(
            precise_rel_start_bound(
                &RelFiniteBoundPos::new(SignedDuration::MAX).to_start_bound(),
                Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

mod precise_rel_start_bound_with_base_offset {
    use super::*;

    #[test]
    fn ok_finite() {
        assert_eq!(
            precise_rel_start_bound_with_base_offset(
                &RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_start_bound(),
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                SignedDuration::from_mins(10)
            ),
            Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(25)).to_start_bound())
        );
    }

    #[test]
    fn ok_infinite() {
        assert_eq!(
            precise_rel_start_bound_with_base_offset(
                &RelStartBound::InfinitePast,
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                SignedDuration::from_mins(10)
            ),
            Ok(RelStartBound::InfinitePast)
        );
    }

    #[test]
    fn precision_out_of_range_error() {
        assert_eq!(
            precise_rel_start_bound_with_base_offset(
                &RelFiniteBoundPos::new(SignedDuration::MAX).to_start_bound(),
                Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                SignedDuration::from_mins(10)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

mod precise_rel_end_bound {
    use super::*;

    #[test]
    fn ok_finite() {
        assert_eq!(
            precise_rel_end_bound(
                &RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_end_bound(),
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
            ),
            Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(30)).to_end_bound())
        );
    }

    #[test]
    fn ok_infinite() {
        assert_eq!(
            precise_rel_end_bound(
                &RelEndBound::InfiniteFuture,
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
            ),
            Ok(RelEndBound::InfiniteFuture)
        );
    }

    #[test]
    fn precision_out_of_range_error() {
        assert_eq!(
            precise_rel_end_bound(
                &RelFiniteBoundPos::new(SignedDuration::MAX).to_end_bound(),
                Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

mod precise_rel_end_bound_with_base_offset {
    use super::*;

    #[test]
    fn ok_finite() {
        assert_eq!(
            precise_rel_end_bound_with_base_offset(
                &RelFiniteBoundPos::new(SignedDuration::from_mins(20)).to_end_bound(),
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                SignedDuration::from_mins(10)
            ),
            Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(25)).to_end_bound())
        );
    }

    #[test]
    fn ok_infinite() {
        assert_eq!(
            precise_rel_end_bound_with_base_offset(
                &RelEndBound::InfiniteFuture,
                Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                SignedDuration::from_mins(10)
            ),
            Ok(RelEndBound::InfiniteFuture)
        );
    }

    #[test]
    fn precision_out_of_range_error() {
        assert_eq!(
            precise_rel_end_bound_with_base_offset(
                &RelFiniteBoundPos::new(SignedDuration::MAX).to_end_bound(),
                Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                SignedDuration::from_mins(10)
            ),
            Err(PrecisionOutOfRangeError)
        );
    }
}

mod precise_rel_bound {
    use super::*;

    mod start {
        use super::*;

        #[test]
        fn ok_finite() {
            assert_eq!(
                precise_rel_bound(
                    &RelFiniteBoundPos::new(SignedDuration::from_mins(20))
                        .to_start_bound()
                        .to_bound(),
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                ),
                Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(30))
                    .to_start_bound()
                    .to_bound())
            );
        }

        #[test]
        fn ok_infinite() {
            assert_eq!(
                precise_rel_bound(
                    &RelStartBound::InfinitePast.to_bound(),
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                ),
                Ok(RelStartBound::InfinitePast.to_bound())
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                precise_rel_bound(
                    &RelFiniteBoundPos::new(SignedDuration::MAX).to_start_bound().to_bound(),
                    Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod end {
        use super::*;

        #[test]
        fn ok_finite() {
            assert_eq!(
                precise_rel_bound(
                    &RelFiniteBoundPos::new(SignedDuration::from_mins(20))
                        .to_end_bound()
                        .to_bound(),
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                ),
                Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(30))
                    .to_end_bound()
                    .to_bound())
            );
        }

        #[test]
        fn ok_infinite() {
            assert_eq!(
                precise_rel_bound(
                    &RelEndBound::InfiniteFuture.to_bound(),
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                ),
                Ok(RelEndBound::InfiniteFuture.to_bound())
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                precise_rel_bound(
                    &RelFiniteBoundPos::new(SignedDuration::MAX).to_end_bound().to_bound(),
                    Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}

mod precise_rel_bound_with_base_offset {
    use super::*;

    mod start {
        use super::*;

        #[test]
        fn ok_finite() {
            assert_eq!(
                precise_rel_bound_with_base_offset(
                    &RelFiniteBoundPos::new(SignedDuration::from_mins(20))
                        .to_start_bound()
                        .to_bound(),
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(10)
                ),
                Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(25))
                    .to_start_bound()
                    .to_bound())
            );
        }

        #[test]
        fn ok_infinite() {
            assert_eq!(
                precise_rel_bound_with_base_offset(
                    &RelStartBound::InfinitePast.to_bound(),
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(10)
                ),
                Ok(RelStartBound::InfinitePast.to_bound())
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                precise_rel_bound_with_base_offset(
                    &RelFiniteBoundPos::new(SignedDuration::MAX).to_start_bound().to_bound(),
                    Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(10)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }

    mod end {
        use super::*;

        #[test]
        fn ok_finite() {
            assert_eq!(
                precise_rel_bound_with_base_offset(
                    &RelFiniteBoundPos::new(SignedDuration::from_mins(20))
                        .to_end_bound()
                        .to_bound(),
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(10)
                ),
                Ok(RelFiniteBoundPos::new(SignedDuration::from_mins(25))
                    .to_end_bound()
                    .to_bound())
            );
        }

        #[test]
        fn ok_infinite() {
            assert_eq!(
                precise_rel_bound_with_base_offset(
                    &RelEndBound::InfiniteFuture.to_bound(),
                    Precision::unchecked_new(Duration::from_mins(15), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(10)
                ),
                Ok(RelEndBound::InfiniteFuture.to_bound())
            );
        }

        #[test]
        fn precision_out_of_range_error() {
            assert_eq!(
                precise_rel_bound_with_base_offset(
                    &RelFiniteBoundPos::new(SignedDuration::MAX).to_end_bound().to_bound(),
                    Precision::unchecked_new(Duration::from_mins(10), PrecisionMode::ToFuture),
                    SignedDuration::from_mins(10)
                ),
                Err(PrecisionOutOfRangeError)
            );
        }
    }
}
