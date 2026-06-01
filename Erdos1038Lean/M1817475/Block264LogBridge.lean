import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block264

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block264

open Set

def block264W1 : Rat := ((32136572901337 : Rat) / 31250000000000)
def block264W2 : Rat := ((6660954440247357 : Rat) / 250000000000000000)
def block264W3 : Rat := ((7423206155957239 : Rat) / 25000000000000000)
def block264W4 : Rat := (0 : Rat)
def block264S1 : Rat := ((18174751 : Rat) / 10000000)
def block264S2 : Rat := ((511587 : Rat) / 200000)
def block264S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block264S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block264V (y : ℝ) : ℝ :=
  ratPotential block264W1 block264W2 block264W3 block264W4 block264S1 block264S2 block264S3 block264S4 y

def block264LeftParamsCertificate : Bool :=
  allBoxesSameParams block264LeftBoxes block264W1 block264W2 block264W3 block264W4 block264S1 block264S2 block264S3 block264S4

theorem block264LeftParamsCertificate_eq_true :
    block264LeftParamsCertificate = true := by
  native_decide

theorem block264_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block264LeftL : ℝ) (block264LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block264S1 : ℝ))
    (hy2ne : y ≠ (block264S2 : ℝ))
    (hy3ne : y ≠ (block264S3 : ℝ))
    (hy4ne : y ≠ (block264S4 : ℝ)) :
    0 < block264V y := by
  have hcert := block264LeftCertificate_eq_true
  unfold block264LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block264LeftBoxes) (lo := block264LeftL) (hi := block264LeftR)
    (w1 := block264W1) (w2 := block264W2) (w3 := block264W3) (w4 := block264W4)
    (s1 := block264S1) (s2 := block264S2) (s3 := block264S3) (s4 := block264S4)
    hboxes hcover block264LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block264RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block264RightChunk000 block264W1 block264W2 block264W3 block264W4 block264S1 block264S2 block264S3 block264S4

theorem block264RightChunk000ParamsCertificate_eq_true :
    block264RightChunk000ParamsCertificate = true := by
  native_decide

theorem block264_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block264RightChunk000L : ℝ) (block264RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block264S1 : ℝ))
    (hy2ne : y ≠ (block264S2 : ℝ))
    (hy3ne : y ≠ (block264S3 : ℝ))
    (hy4ne : y ≠ (block264S4 : ℝ)) :
    0 < block264V y := by
  have hcert := block264RightChunk000Certificate_eq_true
  unfold block264RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block264RightChunk000) (lo := block264RightChunk000L) (hi := block264RightChunk000R)
    (w1 := block264W1) (w2 := block264W2) (w3 := block264W3) (w4 := block264W4)
    (s1 := block264S1) (s2 := block264S2) (s3 := block264S3) (s4 := block264S4)
    hboxes hcover block264RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block264RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block264RightChunk001 block264W1 block264W2 block264W3 block264W4 block264S1 block264S2 block264S3 block264S4

theorem block264RightChunk001ParamsCertificate_eq_true :
    block264RightChunk001ParamsCertificate = true := by
  native_decide

theorem block264_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block264RightChunk001L : ℝ) (block264RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block264S1 : ℝ))
    (hy2ne : y ≠ (block264S2 : ℝ))
    (hy3ne : y ≠ (block264S3 : ℝ))
    (hy4ne : y ≠ (block264S4 : ℝ)) :
    0 < block264V y := by
  have hcert := block264RightChunk001Certificate_eq_true
  unfold block264RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block264RightChunk001) (lo := block264RightChunk001L) (hi := block264RightChunk001R)
    (w1 := block264W1) (w2 := block264W2) (w3 := block264W3) (w4 := block264W4)
    (s1 := block264S1) (s2 := block264S2) (s3 := block264S3) (s4 := block264S4)
    hboxes hcover block264RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block264_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block264RightL : ℝ) (block264RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block264S1 : ℝ))
    (hy2ne : y ≠ (block264S2 : ℝ))
    (hy3ne : y ≠ (block264S3 : ℝ))
    (hy4ne : y ≠ (block264S4 : ℝ)) :
    0 < block264V y := by
  by_cases h0 : y ≤ (block264RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block264RightChunk000L : ℝ) (block264RightChunk000R : ℝ) := by
      have hL : (block264RightChunk000L : ℝ) = (block264RightL : ℝ) := by
        norm_num [block264RightChunk000L, block264RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block264_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block264RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block264RightChunk001L : ℝ) = (block264RightChunk000R : ℝ) := by
      norm_num [block264RightChunk001L, block264RightChunk000R]
    have hR : (block264RightChunk001R : ℝ) = (block264RightR : ℝ) := by
      norm_num [block264RightChunk001R, block264RightR]
    have hyc : y ∈ Icc (block264RightChunk001L : ℝ) (block264RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block264_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block264_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block264LeftL : ℝ) (block264LeftR : ℝ) →
    y ≠ 0 → y ≠ (block264S1 : ℝ) → y ≠ (block264S2 : ℝ) →
    y ≠ (block264S3 : ℝ) → y ≠ (block264S4 : ℝ) → 0 < block264V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block264RightL : ℝ) (block264RightR : ℝ) →
    y ≠ 0 → y ≠ (block264S1 : ℝ) → y ≠ (block264S2 : ℝ) →
    y ≠ (block264S3 : ℝ) → y ≠ (block264S4 : ℝ) → 0 < block264V y)

theorem block264_reallog_certificate_proof :
    block264_reallog_certificate := by
  exact ⟨block264_left_V_pos, block264_right_V_pos⟩

end Block264
end M1817475
end Erdos1038Lean
