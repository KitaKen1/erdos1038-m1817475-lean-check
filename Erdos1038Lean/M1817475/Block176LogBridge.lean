import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block176

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block176

open Set

def block176W1 : Rat := ((900739095401367 : Rat) / 500000000000000)
def block176W2 : Rat := (0 : Rat)
def block176W3 : Rat := ((2140589004642491 : Rat) / 12500000000000000)
def block176W4 : Rat := ((9866152849493061 : Rat) / 100000000000000000)
def block176S1 : Rat := ((18174751 : Rat) / 10000000)
def block176S2 : Rat := ((511587 : Rat) / 200000)
def block176S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block176S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block176V (y : ℝ) : ℝ :=
  ratPotential block176W1 block176W2 block176W3 block176W4 block176S1 block176S2 block176S3 block176S4 y

def block176LeftParamsCertificate : Bool :=
  allBoxesSameParams block176LeftBoxes block176W1 block176W2 block176W3 block176W4 block176S1 block176S2 block176S3 block176S4

theorem block176LeftParamsCertificate_eq_true :
    block176LeftParamsCertificate = true := by
  native_decide

theorem block176_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block176LeftL : ℝ) (block176LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block176S1 : ℝ))
    (hy2ne : y ≠ (block176S2 : ℝ))
    (hy3ne : y ≠ (block176S3 : ℝ))
    (hy4ne : y ≠ (block176S4 : ℝ)) :
    0 < block176V y := by
  have hcert := block176LeftCertificate_eq_true
  unfold block176LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block176LeftBoxes) (lo := block176LeftL) (hi := block176LeftR)
    (w1 := block176W1) (w2 := block176W2) (w3 := block176W3) (w4 := block176W4)
    (s1 := block176S1) (s2 := block176S2) (s3 := block176S3) (s4 := block176S4)
    hboxes hcover block176LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block176RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block176RightChunk000 block176W1 block176W2 block176W3 block176W4 block176S1 block176S2 block176S3 block176S4

theorem block176RightChunk000ParamsCertificate_eq_true :
    block176RightChunk000ParamsCertificate = true := by
  native_decide

theorem block176_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block176RightChunk000L : ℝ) (block176RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block176S1 : ℝ))
    (hy2ne : y ≠ (block176S2 : ℝ))
    (hy3ne : y ≠ (block176S3 : ℝ))
    (hy4ne : y ≠ (block176S4 : ℝ)) :
    0 < block176V y := by
  have hcert := block176RightChunk000Certificate_eq_true
  unfold block176RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block176RightChunk000) (lo := block176RightChunk000L) (hi := block176RightChunk000R)
    (w1 := block176W1) (w2 := block176W2) (w3 := block176W3) (w4 := block176W4)
    (s1 := block176S1) (s2 := block176S2) (s3 := block176S3) (s4 := block176S4)
    hboxes hcover block176RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block176RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block176RightChunk001 block176W1 block176W2 block176W3 block176W4 block176S1 block176S2 block176S3 block176S4

theorem block176RightChunk001ParamsCertificate_eq_true :
    block176RightChunk001ParamsCertificate = true := by
  native_decide

theorem block176_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block176RightChunk001L : ℝ) (block176RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block176S1 : ℝ))
    (hy2ne : y ≠ (block176S2 : ℝ))
    (hy3ne : y ≠ (block176S3 : ℝ))
    (hy4ne : y ≠ (block176S4 : ℝ)) :
    0 < block176V y := by
  have hcert := block176RightChunk001Certificate_eq_true
  unfold block176RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block176RightChunk001) (lo := block176RightChunk001L) (hi := block176RightChunk001R)
    (w1 := block176W1) (w2 := block176W2) (w3 := block176W3) (w4 := block176W4)
    (s1 := block176S1) (s2 := block176S2) (s3 := block176S3) (s4 := block176S4)
    hboxes hcover block176RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block176_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block176RightL : ℝ) (block176RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block176S1 : ℝ))
    (hy2ne : y ≠ (block176S2 : ℝ))
    (hy3ne : y ≠ (block176S3 : ℝ))
    (hy4ne : y ≠ (block176S4 : ℝ)) :
    0 < block176V y := by
  by_cases h0 : y ≤ (block176RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block176RightChunk000L : ℝ) (block176RightChunk000R : ℝ) := by
      have hL : (block176RightChunk000L : ℝ) = (block176RightL : ℝ) := by
        norm_num [block176RightChunk000L, block176RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block176_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block176RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block176RightChunk001L : ℝ) = (block176RightChunk000R : ℝ) := by
      norm_num [block176RightChunk001L, block176RightChunk000R]
    have hR : (block176RightChunk001R : ℝ) = (block176RightR : ℝ) := by
      norm_num [block176RightChunk001R, block176RightR]
    have hyc : y ∈ Icc (block176RightChunk001L : ℝ) (block176RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block176_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block176_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block176LeftL : ℝ) (block176LeftR : ℝ) →
    y ≠ 0 → y ≠ (block176S1 : ℝ) → y ≠ (block176S2 : ℝ) →
    y ≠ (block176S3 : ℝ) → y ≠ (block176S4 : ℝ) → 0 < block176V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block176RightL : ℝ) (block176RightR : ℝ) →
    y ≠ 0 → y ≠ (block176S1 : ℝ) → y ≠ (block176S2 : ℝ) →
    y ≠ (block176S3 : ℝ) → y ≠ (block176S4 : ℝ) → 0 < block176V y)

theorem block176_reallog_certificate_proof :
    block176_reallog_certificate := by
  exact ⟨block176_left_V_pos, block176_right_V_pos⟩

end Block176
end M1817475
end Erdos1038Lean
