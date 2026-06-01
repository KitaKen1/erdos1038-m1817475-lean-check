import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block414

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block414

open Set

def block414W1 : Rat := ((7055321144078249 : Rat) / 10000000000000000)
def block414W2 : Rat := (0 : Rat)
def block414W3 : Rat := ((1452019497829221 : Rat) / 5000000000000000)
def block414W4 : Rat := ((8780317597614513 : Rat) / 100000000000000000)
def block414S1 : Rat := ((18174751 : Rat) / 10000000)
def block414S2 : Rat := ((511587 : Rat) / 200000)
def block414S3 : Rat := ((5281609075000000003 : Rat) / 2000000000000000000)
def block414S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block414V (y : ℝ) : ℝ :=
  ratPotential block414W1 block414W2 block414W3 block414W4 block414S1 block414S2 block414S3 block414S4 y

def block414LeftParamsCertificate : Bool :=
  allBoxesSameParams block414LeftBoxes block414W1 block414W2 block414W3 block414W4 block414S1 block414S2 block414S3 block414S4

theorem block414LeftParamsCertificate_eq_true :
    block414LeftParamsCertificate = true := by
  native_decide

theorem block414_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block414LeftL : ℝ) (block414LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block414S1 : ℝ))
    (hy2ne : y ≠ (block414S2 : ℝ))
    (hy3ne : y ≠ (block414S3 : ℝ))
    (hy4ne : y ≠ (block414S4 : ℝ)) :
    0 < block414V y := by
  have hcert := block414LeftCertificate_eq_true
  unfold block414LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block414LeftBoxes) (lo := block414LeftL) (hi := block414LeftR)
    (w1 := block414W1) (w2 := block414W2) (w3 := block414W3) (w4 := block414W4)
    (s1 := block414S1) (s2 := block414S2) (s3 := block414S3) (s4 := block414S4)
    hboxes hcover block414LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block414RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block414RightChunk000 block414W1 block414W2 block414W3 block414W4 block414S1 block414S2 block414S3 block414S4

theorem block414RightChunk000ParamsCertificate_eq_true :
    block414RightChunk000ParamsCertificate = true := by
  native_decide

theorem block414_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block414RightChunk000L : ℝ) (block414RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block414S1 : ℝ))
    (hy2ne : y ≠ (block414S2 : ℝ))
    (hy3ne : y ≠ (block414S3 : ℝ))
    (hy4ne : y ≠ (block414S4 : ℝ)) :
    0 < block414V y := by
  have hcert := block414RightChunk000Certificate_eq_true
  unfold block414RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block414RightChunk000) (lo := block414RightChunk000L) (hi := block414RightChunk000R)
    (w1 := block414W1) (w2 := block414W2) (w3 := block414W3) (w4 := block414W4)
    (s1 := block414S1) (s2 := block414S2) (s3 := block414S3) (s4 := block414S4)
    hboxes hcover block414RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block414RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block414RightChunk001 block414W1 block414W2 block414W3 block414W4 block414S1 block414S2 block414S3 block414S4

theorem block414RightChunk001ParamsCertificate_eq_true :
    block414RightChunk001ParamsCertificate = true := by
  native_decide

theorem block414_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block414RightChunk001L : ℝ) (block414RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block414S1 : ℝ))
    (hy2ne : y ≠ (block414S2 : ℝ))
    (hy3ne : y ≠ (block414S3 : ℝ))
    (hy4ne : y ≠ (block414S4 : ℝ)) :
    0 < block414V y := by
  have hcert := block414RightChunk001Certificate_eq_true
  unfold block414RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block414RightChunk001) (lo := block414RightChunk001L) (hi := block414RightChunk001R)
    (w1 := block414W1) (w2 := block414W2) (w3 := block414W3) (w4 := block414W4)
    (s1 := block414S1) (s2 := block414S2) (s3 := block414S3) (s4 := block414S4)
    hboxes hcover block414RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block414_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block414RightL : ℝ) (block414RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block414S1 : ℝ))
    (hy2ne : y ≠ (block414S2 : ℝ))
    (hy3ne : y ≠ (block414S3 : ℝ))
    (hy4ne : y ≠ (block414S4 : ℝ)) :
    0 < block414V y := by
  by_cases h0 : y ≤ (block414RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block414RightChunk000L : ℝ) (block414RightChunk000R : ℝ) := by
      have hL : (block414RightChunk000L : ℝ) = (block414RightL : ℝ) := by
        norm_num [block414RightChunk000L, block414RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block414_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block414RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block414RightChunk001L : ℝ) = (block414RightChunk000R : ℝ) := by
      norm_num [block414RightChunk001L, block414RightChunk000R]
    have hR : (block414RightChunk001R : ℝ) = (block414RightR : ℝ) := by
      norm_num [block414RightChunk001R, block414RightR]
    have hyc : y ∈ Icc (block414RightChunk001L : ℝ) (block414RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block414_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block414_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block414LeftL : ℝ) (block414LeftR : ℝ) →
    y ≠ 0 → y ≠ (block414S1 : ℝ) → y ≠ (block414S2 : ℝ) →
    y ≠ (block414S3 : ℝ) → y ≠ (block414S4 : ℝ) → 0 < block414V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block414RightL : ℝ) (block414RightR : ℝ) →
    y ≠ 0 → y ≠ (block414S1 : ℝ) → y ≠ (block414S2 : ℝ) →
    y ≠ (block414S3 : ℝ) → y ≠ (block414S4 : ℝ) → 0 < block414V y)

theorem block414_reallog_certificate_proof :
    block414_reallog_certificate := by
  exact ⟨block414_left_V_pos, block414_right_V_pos⟩

end Block414
end M1817475
end Erdos1038Lean
