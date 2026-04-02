use super::state::*;

#[test]
fn is_first_layer_active() {
    assert!(!LayeredBoundsState::NoLayers.is_first_layer_active());
    assert!(LayeredBoundsState::FirstLayer.is_first_layer_active());
    assert!(!LayeredBoundsState::SecondLayer.is_first_layer_active());
    assert!(LayeredBoundsState::BothLayers.is_first_layer_active());
}

#[test]
fn is_second_layer_active() {
    assert!(!LayeredBoundsState::NoLayers.is_second_layer_active());
    assert!(!LayeredBoundsState::FirstLayer.is_second_layer_active());
    assert!(LayeredBoundsState::SecondLayer.is_second_layer_active());
    assert!(LayeredBoundsState::BothLayers.is_second_layer_active());
}

#[test]
fn add_no_layers_no_layers() {
    assert_eq!(
        LayeredBoundsState::NoLayers + LayeredBoundsState::NoLayers,
        LayeredBoundsState::NoLayers
    );
}

#[test]
fn add_no_layers_first_layer() {
    assert_eq!(
        LayeredBoundsState::NoLayers + LayeredBoundsState::FirstLayer,
        LayeredBoundsState::FirstLayer
    );
}

#[test]
fn add_no_layers_second_layer() {
    assert_eq!(
        LayeredBoundsState::NoLayers + LayeredBoundsState::SecondLayer,
        LayeredBoundsState::SecondLayer
    );
}

#[test]
fn add_no_layers_both_layers() {
    assert_eq!(
        LayeredBoundsState::NoLayers + LayeredBoundsState::BothLayers,
        LayeredBoundsState::BothLayers
    );
}

#[test]
fn add_first_layer_no_layers() {
    assert_eq!(
        LayeredBoundsState::FirstLayer + LayeredBoundsState::NoLayers,
        LayeredBoundsState::FirstLayer
    );
}

#[test]
fn add_first_layer_first_layer() {
    assert_eq!(
        LayeredBoundsState::FirstLayer + LayeredBoundsState::FirstLayer,
        LayeredBoundsState::FirstLayer
    );
}

#[test]
fn add_first_layer_second_layer() {
    assert_eq!(
        LayeredBoundsState::FirstLayer + LayeredBoundsState::SecondLayer,
        LayeredBoundsState::BothLayers
    );
}

#[test]
fn add_first_layer_both_layers() {
    assert_eq!(
        LayeredBoundsState::FirstLayer + LayeredBoundsState::BothLayers,
        LayeredBoundsState::BothLayers
    );
}

#[test]
fn add_second_layer_no_layers() {
    assert_eq!(
        LayeredBoundsState::SecondLayer + LayeredBoundsState::NoLayers,
        LayeredBoundsState::SecondLayer
    );
}

#[test]
fn add_second_layer_first_layer() {
    assert_eq!(
        LayeredBoundsState::SecondLayer + LayeredBoundsState::FirstLayer,
        LayeredBoundsState::BothLayers
    );
}

#[test]
fn add_second_layer_second_layer() {
    assert_eq!(
        LayeredBoundsState::SecondLayer + LayeredBoundsState::SecondLayer,
        LayeredBoundsState::SecondLayer
    );
}

#[test]
fn add_second_layer_both_layers() {
    assert_eq!(
        LayeredBoundsState::SecondLayer + LayeredBoundsState::BothLayers,
        LayeredBoundsState::BothLayers
    );
}

#[test]
fn add_both_layers_no_layers() {
    assert_eq!(
        LayeredBoundsState::BothLayers + LayeredBoundsState::NoLayers,
        LayeredBoundsState::BothLayers
    );
}

#[test]
fn add_both_layers_first_layer() {
    assert_eq!(
        LayeredBoundsState::BothLayers + LayeredBoundsState::FirstLayer,
        LayeredBoundsState::BothLayers
    );
}

#[test]
fn add_both_layers_second_layer() {
    assert_eq!(
        LayeredBoundsState::BothLayers + LayeredBoundsState::SecondLayer,
        LayeredBoundsState::BothLayers
    );
}

#[test]
fn add_both_layers_both_layers() {
    assert_eq!(
        LayeredBoundsState::BothLayers + LayeredBoundsState::BothLayers,
        LayeredBoundsState::BothLayers
    );
}

#[test]
fn sub_no_layers_no_layers() {
    assert_eq!(
        LayeredBoundsState::NoLayers - LayeredBoundsState::NoLayers,
        LayeredBoundsState::NoLayers
    );
}

#[test]
fn sub_no_layers_first_layer() {
    assert_eq!(
        LayeredBoundsState::NoLayers - LayeredBoundsState::FirstLayer,
        LayeredBoundsState::NoLayers
    );
}

#[test]
fn sub_no_layers_second_layer() {
    assert_eq!(
        LayeredBoundsState::NoLayers - LayeredBoundsState::SecondLayer,
        LayeredBoundsState::NoLayers
    );
}

#[test]
fn sub_no_layers_both_layers() {
    assert_eq!(
        LayeredBoundsState::NoLayers - LayeredBoundsState::BothLayers,
        LayeredBoundsState::NoLayers
    );
}

#[test]
fn sub_first_layer_no_layers() {
    assert_eq!(
        LayeredBoundsState::FirstLayer - LayeredBoundsState::NoLayers,
        LayeredBoundsState::FirstLayer
    );
}

#[test]
fn sub_first_layer_first_layer() {
    assert_eq!(
        LayeredBoundsState::FirstLayer - LayeredBoundsState::FirstLayer,
        LayeredBoundsState::NoLayers
    );
}

#[test]
fn sub_first_layer_second_layer() {
    assert_eq!(
        LayeredBoundsState::FirstLayer - LayeredBoundsState::SecondLayer,
        LayeredBoundsState::FirstLayer
    );
}

#[test]
fn sub_first_layer_both_layers() {
    assert_eq!(
        LayeredBoundsState::FirstLayer - LayeredBoundsState::BothLayers,
        LayeredBoundsState::NoLayers
    );
}

#[test]
fn sub_second_layer_no_layers() {
    assert_eq!(
        LayeredBoundsState::SecondLayer - LayeredBoundsState::NoLayers,
        LayeredBoundsState::SecondLayer
    );
}

#[test]
fn sub_second_layer_first_layer() {
    assert_eq!(
        LayeredBoundsState::SecondLayer - LayeredBoundsState::FirstLayer,
        LayeredBoundsState::SecondLayer
    );
}

#[test]
fn sub_second_layer_second_layer() {
    assert_eq!(
        LayeredBoundsState::SecondLayer - LayeredBoundsState::SecondLayer,
        LayeredBoundsState::NoLayers
    );
}

#[test]
fn sub_second_layer_both_layers() {
    assert_eq!(
        LayeredBoundsState::SecondLayer - LayeredBoundsState::BothLayers,
        LayeredBoundsState::NoLayers
    );
}

#[test]
fn sub_both_layers_no_layers() {
    assert_eq!(
        LayeredBoundsState::BothLayers - LayeredBoundsState::NoLayers,
        LayeredBoundsState::BothLayers
    );
}

#[test]
fn sub_both_layers_first_layer() {
    assert_eq!(
        LayeredBoundsState::BothLayers - LayeredBoundsState::FirstLayer,
        LayeredBoundsState::SecondLayer
    );
}

#[test]
fn sub_both_layers_second_layer() {
    assert_eq!(
        LayeredBoundsState::BothLayers - LayeredBoundsState::SecondLayer,
        LayeredBoundsState::FirstLayer
    );
}

#[test]
fn sub_both_layers_both_layers() {
    assert_eq!(
        LayeredBoundsState::BothLayers - LayeredBoundsState::BothLayers,
        LayeredBoundsState::NoLayers
    );
}
