import Splay.Accounting.LogHeightChocolate

namespace Splay.Accounting.OfflineConnectedSupport.LogHeightChocolate

open Splay.Tree OfflineNormalForm

/-- Weighted depth telescopes across the half-weight links between active
layers and through the frozen icing stack. All logarithms are integer lower
binary logarithms, so the estimate also covers unit payloads exactly. -/
theorem Chocolate.weightedHeight_le {kind : Bool} {level lower upper : ℕ} {tree : BST lower upper}
    (shaped : Chocolate kind level tree) :
    weightedHeight shaped.selected ≤ 7 * logMass tree + level + (if kind then 4 else 8) := by
  induction shaped with
  | base crumb =>
      have bound := crumb.weightedHeight_le
      simp only [Chocolate.selected, Bool.false_eq_true, if_false]
      omega
  | @oneEnd level lower k0 upper a icing crumb0 frozen ihIcing =>
      have crumbBound0 := crumb0.weightedHeight_le
      have crumbLog0 := logMass_mono (before := a) (after := (.node a icing))
        (by simp only [mass, BST.size]; omega)
      have icingLog := logMass_mono (before := icing) (after := (.node a icing))
        (by simp only [mass, BST.size]; omega)
      simp only [Chocolate.selected, weightedHeight, Bool.false_eq_true, if_false, if_true] at *
      omega
  | @twoEnd level lower k0 k1 upper a b icing crumb0 crumb1 frozen ihIcing =>
      have crumbBound0 := crumb0.weightedHeight_le
      have crumbLog0 := logMass_mono (before := a) (after := (.node a (.node b icing)))
        (by simp only [mass, BST.size]; omega)
      have crumbBound1 := crumb1.weightedHeight_le
      have crumbLog1 := logMass_mono (before := b) (after := (.node a (.node b icing)))
        (by simp only [mass, BST.size]; omega)
      have icingLog := logMass_mono (before := icing) (after := (.node a (.node b icing)))
        (by simp only [mass, BST.size]; omega)
      simp only [Chocolate.selected, weightedHeight, Bool.false_eq_true, if_false, if_true] at *
      omega
  | @threeEnd level lower k0 k1 k2 upper a b c icing crumb0 crumb1 crumb2 frozen ihIcing =>
      have crumbBound0 := crumb0.weightedHeight_le
      have crumbLog0 := logMass_mono (before := a) (after := (.node a (.node b (.node c icing))))
        (by simp only [mass, BST.size]; omega)
      have crumbBound1 := crumb1.weightedHeight_le
      have crumbLog1 := logMass_mono (before := b) (after := (.node a (.node b (.node c icing))))
        (by simp only [mass, BST.size]; omega)
      have crumbBound2 := crumb2.weightedHeight_le
      have crumbLog2 := logMass_mono (before := c) (after := (.node a (.node b (.node c icing))))
        (by simp only [mass, BST.size]; omega)
      have icingLog := logMass_mono (before := icing) (after := (.node a (.node b (.node c icing))))
        (by simp only [mass, BST.size]; omega)
      simp only [Chocolate.selected, weightedHeight, Bool.false_eq_true, if_false, if_true] at *
      omega
  | @oneNext level lower k0 pivot upper a next icing crumb0 layer frozen thin ihLayer ihIcing =>
      have crumbBound0 := crumb0.weightedHeight_le
      have crumbLog0 := logMass_mono (before := a) (after := (.node a (.node next icing)))
        (by simp only [mass, BST.size]; omega)
      have icingLog := logMass_mono (before := icing) (after := (.node a (.node next icing)))
        (by simp only [mass, BST.size]; omega)
      have layerLog := logMass_half (before := next) (after := (.node a (.node next icing)))
        (by simp only [mass, BST.size] at thin ⊢; omega)
      simp only [Chocolate.selected, weightedHeight, Bool.false_eq_true, if_false, if_true] at *
      omega
  | @twoNext level lower k0 k1 pivot upper a b next icing crumb0 crumb1 layer frozen thin ihLayer ihIcing =>
      have crumbBound0 := crumb0.weightedHeight_le
      have crumbLog0 := logMass_mono (before := a) (after := (.node a (.node b (.node next icing))))
        (by simp only [mass, BST.size]; omega)
      have crumbBound1 := crumb1.weightedHeight_le
      have crumbLog1 := logMass_mono (before := b) (after := (.node a (.node b (.node next icing))))
        (by simp only [mass, BST.size]; omega)
      have icingLog := logMass_mono (before := icing) (after := (.node a (.node b (.node next icing))))
        (by simp only [mass, BST.size]; omega)
      have layerLog := logMass_half (before := next) (after := (.node a (.node b (.node next icing))))
        (by simp only [mass, BST.size] at thin ⊢; omega)
      simp only [Chocolate.selected, weightedHeight, Bool.false_eq_true, if_false, if_true] at *
      omega
  | @threeNext level lower k0 k1 k2 pivot upper a b c next icing crumb0 crumb1 crumb2 layer frozen thin ihLayer ihIcing =>
      have crumbBound0 := crumb0.weightedHeight_le
      have crumbLog0 := logMass_mono (before := a) (after := (.node a (.node b (.node c (.node next icing)))))
        (by simp only [mass, BST.size]; omega)
      have crumbBound1 := crumb1.weightedHeight_le
      have crumbLog1 := logMass_mono (before := b) (after := (.node a (.node b (.node c (.node next icing)))))
        (by simp only [mass, BST.size]; omega)
      have crumbBound2 := crumb2.weightedHeight_le
      have crumbLog2 := logMass_mono (before := c) (after := (.node a (.node b (.node c (.node next icing)))))
        (by simp only [mass, BST.size]; omega)
      have icingLog := logMass_mono (before := icing) (after := (.node a (.node b (.node c (.node next icing)))))
        (by simp only [mass, BST.size]; omega)
      have layerLog := logMass_half (before := next) (after := (.node a (.node b (.node c (.node next icing)))))
        (by simp only [mass, BST.size] at thin ⊢; omega)
      simp only [Chocolate.selected, weightedHeight, Bool.false_eq_true, if_false, if_true] at *
      omega
  | icingBase crumb =>
      have bound := crumb.weightedHeight_le
      simp only [Chocolate.selected, if_true]
      omega
  | @freezeCrumb level lower root upper crumbTree icing crumb frozen thick ihIcing =>
      have crumbBound := crumb.weightedHeight_le
      have crumbLog := logMass_mono (before := crumbTree) (after := BST.node crumbTree icing)
        (by simp only [mass, BST.size]; omega)
      have icingLog := logMass_half (before := icing) (after := BST.node crumbTree icing)
        (by simp only [mass, BST.size] at thick ⊢; omega)
      simp only [Chocolate.selected, weightedHeight, if_true] at *
      omega
  | @freezeLayer level lower first second upper crumbTree next icing crumb layer frozen thin thick ihLayer ihIcing =>
      have crumbBound := crumb.weightedHeight_le
      have crumbLog := logMass_mono (before := crumbTree) (after := BST.node (.node crumbTree next) icing)
        (by simp only [mass, BST.size]; omega)
      have layerLog := logMass_half (before := next) (after := BST.node (.node crumbTree next) icing)
        (by simp only [mass, BST.size] at thin ⊢; omega)
      have icingLog := logMass_half (before := icing) (after := BST.node (.node crumbTree next) icing)
        (by simp only [mass, BST.size] at thick ⊢; omega)
      simp only [Chocolate.selected, weightedHeight, Bool.false_eq_true, if_false, if_true] at *
      omega

end Splay.Accounting.OfflineConnectedSupport.LogHeightChocolate
