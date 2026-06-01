import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block236

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block236

open Set

def block236W1 : Rat := ((4315607331363131 : Rat) / 5000000000000000)
def block236W2 : Rat := ((4214498538830861 : Rat) / 50000000000000000)
def block236W3 : Rat := ((2267350006804153 : Rat) / 12500000000000000)
def block236W4 : Rat := ((1108975505959 : Rat) / 15625000000000)
def block236S1 : Rat := ((18174751 : Rat) / 10000000)
def block236S2 : Rat := ((511587 : Rat) / 200000)
def block236S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block236S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block236V (y : ℝ) : ℝ :=
  ratPotential block236W1 block236W2 block236W3 block236W4 block236S1 block236S2 block236S3 block236S4 y

def block236LeftParamsCertificate : Bool :=
  allBoxesSameParams block236LeftBoxes block236W1 block236W2 block236W3 block236W4 block236S1 block236S2 block236S3 block236S4

theorem block236LeftParamsCertificate_eq_true :
    block236LeftParamsCertificate = true := by
  native_decide

theorem block236_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block236LeftL : ℝ) (block236LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block236S1 : ℝ))
    (hy2ne : y ≠ (block236S2 : ℝ))
    (hy3ne : y ≠ (block236S3 : ℝ))
    (hy4ne : y ≠ (block236S4 : ℝ)) :
    0 < block236V y := by
  have hcert := block236LeftCertificate_eq_true
  unfold block236LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block236LeftBoxes) (lo := block236LeftL) (hi := block236LeftR)
    (w1 := block236W1) (w2 := block236W2) (w3 := block236W3) (w4 := block236W4)
    (s1 := block236S1) (s2 := block236S2) (s3 := block236S3) (s4 := block236S4)
    hboxes hcover block236LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block236RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block236RightChunk000 block236W1 block236W2 block236W3 block236W4 block236S1 block236S2 block236S3 block236S4

theorem block236RightChunk000ParamsCertificate_eq_true :
    block236RightChunk000ParamsCertificate = true := by
  native_decide

theorem block236_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block236RightChunk000L : ℝ) (block236RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block236S1 : ℝ))
    (hy2ne : y ≠ (block236S2 : ℝ))
    (hy3ne : y ≠ (block236S3 : ℝ))
    (hy4ne : y ≠ (block236S4 : ℝ)) :
    0 < block236V y := by
  have hcert := block236RightChunk000Certificate_eq_true
  unfold block236RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block236RightChunk000) (lo := block236RightChunk000L) (hi := block236RightChunk000R)
    (w1 := block236W1) (w2 := block236W2) (w3 := block236W3) (w4 := block236W4)
    (s1 := block236S1) (s2 := block236S2) (s3 := block236S3) (s4 := block236S4)
    hboxes hcover block236RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block236RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block236RightChunk001 block236W1 block236W2 block236W3 block236W4 block236S1 block236S2 block236S3 block236S4

theorem block236RightChunk001ParamsCertificate_eq_true :
    block236RightChunk001ParamsCertificate = true := by
  native_decide

theorem block236_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block236RightChunk001L : ℝ) (block236RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block236S1 : ℝ))
    (hy2ne : y ≠ (block236S2 : ℝ))
    (hy3ne : y ≠ (block236S3 : ℝ))
    (hy4ne : y ≠ (block236S4 : ℝ)) :
    0 < block236V y := by
  have hcert := block236RightChunk001Certificate_eq_true
  unfold block236RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block236RightChunk001) (lo := block236RightChunk001L) (hi := block236RightChunk001R)
    (w1 := block236W1) (w2 := block236W2) (w3 := block236W3) (w4 := block236W4)
    (s1 := block236S1) (s2 := block236S2) (s3 := block236S3) (s4 := block236S4)
    hboxes hcover block236RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block236_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block236RightL : ℝ) (block236RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block236S1 : ℝ))
    (hy2ne : y ≠ (block236S2 : ℝ))
    (hy3ne : y ≠ (block236S3 : ℝ))
    (hy4ne : y ≠ (block236S4 : ℝ)) :
    0 < block236V y := by
  by_cases h0 : y ≤ (block236RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block236RightChunk000L : ℝ) (block236RightChunk000R : ℝ) := by
      have hL : (block236RightChunk000L : ℝ) = (block236RightL : ℝ) := by
        norm_num [block236RightChunk000L, block236RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block236_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block236RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block236RightChunk001L : ℝ) = (block236RightChunk000R : ℝ) := by
      norm_num [block236RightChunk001L, block236RightChunk000R]
    have hR : (block236RightChunk001R : ℝ) = (block236RightR : ℝ) := by
      norm_num [block236RightChunk001R, block236RightR]
    have hyc : y ∈ Icc (block236RightChunk001L : ℝ) (block236RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block236_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block236_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block236LeftL : ℝ) (block236LeftR : ℝ) →
    y ≠ 0 → y ≠ (block236S1 : ℝ) → y ≠ (block236S2 : ℝ) →
    y ≠ (block236S3 : ℝ) → y ≠ (block236S4 : ℝ) → 0 < block236V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block236RightL : ℝ) (block236RightR : ℝ) →
    y ≠ 0 → y ≠ (block236S1 : ℝ) → y ≠ (block236S2 : ℝ) →
    y ≠ (block236S3 : ℝ) → y ≠ (block236S4 : ℝ) → 0 < block236V y)

theorem block236_reallog_certificate_proof :
    block236_reallog_certificate := by
  exact ⟨block236_left_V_pos, block236_right_V_pos⟩

end Block236
end M1817475
end Erdos1038Lean
