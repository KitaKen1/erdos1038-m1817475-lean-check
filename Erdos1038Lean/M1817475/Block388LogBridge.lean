import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block388

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block388

open Set

def block388W1 : Rat := ((8101058823017069 : Rat) / 10000000000000000)
def block388W2 : Rat := ((10375980494313661 : Rat) / 250000000000000000)
def block388W3 : Rat := ((17015423113646483 : Rat) / 100000000000000000)
def block388W4 : Rat := ((7284535839301323 : Rat) / 50000000000000000)
def block388S1 : Rat := ((18174751 : Rat) / 10000000)
def block388S2 : Rat := ((511587 : Rat) / 200000)
def block388S3 : Rat := ((132548503660714285767 : Rat) / 50000000000000000000)
def block388S4 : Rat := ((34776808526785713037 : Rat) / 12500000000000000000)

noncomputable def block388V (y : ℝ) : ℝ :=
  ratPotential block388W1 block388W2 block388W3 block388W4 block388S1 block388S2 block388S3 block388S4 y

def block388LeftParamsCertificate : Bool :=
  allBoxesSameParams block388LeftBoxes block388W1 block388W2 block388W3 block388W4 block388S1 block388S2 block388S3 block388S4

theorem block388LeftParamsCertificate_eq_true :
    block388LeftParamsCertificate = true := by
  native_decide

theorem block388_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block388LeftL : ℝ) (block388LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block388S1 : ℝ))
    (hy2ne : y ≠ (block388S2 : ℝ))
    (hy3ne : y ≠ (block388S3 : ℝ))
    (hy4ne : y ≠ (block388S4 : ℝ)) :
    0 < block388V y := by
  have hcert := block388LeftCertificate_eq_true
  unfold block388LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block388LeftBoxes) (lo := block388LeftL) (hi := block388LeftR)
    (w1 := block388W1) (w2 := block388W2) (w3 := block388W3) (w4 := block388W4)
    (s1 := block388S1) (s2 := block388S2) (s3 := block388S3) (s4 := block388S4)
    hboxes hcover block388LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block388RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block388RightChunk000 block388W1 block388W2 block388W3 block388W4 block388S1 block388S2 block388S3 block388S4

theorem block388RightChunk000ParamsCertificate_eq_true :
    block388RightChunk000ParamsCertificate = true := by
  native_decide

theorem block388_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block388RightChunk000L : ℝ) (block388RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block388S1 : ℝ))
    (hy2ne : y ≠ (block388S2 : ℝ))
    (hy3ne : y ≠ (block388S3 : ℝ))
    (hy4ne : y ≠ (block388S4 : ℝ)) :
    0 < block388V y := by
  have hcert := block388RightChunk000Certificate_eq_true
  unfold block388RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block388RightChunk000) (lo := block388RightChunk000L) (hi := block388RightChunk000R)
    (w1 := block388W1) (w2 := block388W2) (w3 := block388W3) (w4 := block388W4)
    (s1 := block388S1) (s2 := block388S2) (s3 := block388S3) (s4 := block388S4)
    hboxes hcover block388RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block388RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block388RightChunk001 block388W1 block388W2 block388W3 block388W4 block388S1 block388S2 block388S3 block388S4

theorem block388RightChunk001ParamsCertificate_eq_true :
    block388RightChunk001ParamsCertificate = true := by
  native_decide

theorem block388_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block388RightChunk001L : ℝ) (block388RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block388S1 : ℝ))
    (hy2ne : y ≠ (block388S2 : ℝ))
    (hy3ne : y ≠ (block388S3 : ℝ))
    (hy4ne : y ≠ (block388S4 : ℝ)) :
    0 < block388V y := by
  have hcert := block388RightChunk001Certificate_eq_true
  unfold block388RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block388RightChunk001) (lo := block388RightChunk001L) (hi := block388RightChunk001R)
    (w1 := block388W1) (w2 := block388W2) (w3 := block388W3) (w4 := block388W4)
    (s1 := block388S1) (s2 := block388S2) (s3 := block388S3) (s4 := block388S4)
    hboxes hcover block388RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block388_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block388RightL : ℝ) (block388RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block388S1 : ℝ))
    (hy2ne : y ≠ (block388S2 : ℝ))
    (hy3ne : y ≠ (block388S3 : ℝ))
    (hy4ne : y ≠ (block388S4 : ℝ)) :
    0 < block388V y := by
  by_cases h0 : y ≤ (block388RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block388RightChunk000L : ℝ) (block388RightChunk000R : ℝ) := by
      have hL : (block388RightChunk000L : ℝ) = (block388RightL : ℝ) := by
        norm_num [block388RightChunk000L, block388RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block388_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block388RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block388RightChunk001L : ℝ) = (block388RightChunk000R : ℝ) := by
      norm_num [block388RightChunk001L, block388RightChunk000R]
    have hR : (block388RightChunk001R : ℝ) = (block388RightR : ℝ) := by
      norm_num [block388RightChunk001R, block388RightR]
    have hyc : y ∈ Icc (block388RightChunk001L : ℝ) (block388RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block388_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block388_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block388LeftL : ℝ) (block388LeftR : ℝ) →
    y ≠ 0 → y ≠ (block388S1 : ℝ) → y ≠ (block388S2 : ℝ) →
    y ≠ (block388S3 : ℝ) → y ≠ (block388S4 : ℝ) → 0 < block388V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block388RightL : ℝ) (block388RightR : ℝ) →
    y ≠ 0 → y ≠ (block388S1 : ℝ) → y ≠ (block388S2 : ℝ) →
    y ≠ (block388S3 : ℝ) → y ≠ (block388S4 : ℝ) → 0 < block388V y)

theorem block388_reallog_certificate_proof :
    block388_reallog_certificate := by
  exact ⟨block388_left_V_pos, block388_right_V_pos⟩

end Block388
end M1817475
end Erdos1038Lean
