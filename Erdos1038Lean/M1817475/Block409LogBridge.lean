import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block409

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block409

open Set

def block409W1 : Rat := ((901900472536917 : Rat) / 1250000000000000)
def block409W2 : Rat := (0 : Rat)
def block409W3 : Rat := ((2852425951260279 : Rat) / 10000000000000000)
def block409W4 : Rat := ((9004195335220731 : Rat) / 100000000000000000)
def block409S1 : Rat := ((18174751 : Rat) / 10000000)
def block409S2 : Rat := ((511587 : Rat) / 200000)
def block409S3 : Rat := ((26427594482142857157 : Rat) / 10000000000000000000)
def block409S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block409V (y : ℝ) : ℝ :=
  ratPotential block409W1 block409W2 block409W3 block409W4 block409S1 block409S2 block409S3 block409S4 y

def block409LeftParamsCertificate : Bool :=
  allBoxesSameParams block409LeftBoxes block409W1 block409W2 block409W3 block409W4 block409S1 block409S2 block409S3 block409S4

theorem block409LeftParamsCertificate_eq_true :
    block409LeftParamsCertificate = true := by
  native_decide

theorem block409_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block409LeftL : ℝ) (block409LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block409S1 : ℝ))
    (hy2ne : y ≠ (block409S2 : ℝ))
    (hy3ne : y ≠ (block409S3 : ℝ))
    (hy4ne : y ≠ (block409S4 : ℝ)) :
    0 < block409V y := by
  have hcert := block409LeftCertificate_eq_true
  unfold block409LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block409LeftBoxes) (lo := block409LeftL) (hi := block409LeftR)
    (w1 := block409W1) (w2 := block409W2) (w3 := block409W3) (w4 := block409W4)
    (s1 := block409S1) (s2 := block409S2) (s3 := block409S3) (s4 := block409S4)
    hboxes hcover block409LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block409RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block409RightChunk000 block409W1 block409W2 block409W3 block409W4 block409S1 block409S2 block409S3 block409S4

theorem block409RightChunk000ParamsCertificate_eq_true :
    block409RightChunk000ParamsCertificate = true := by
  native_decide

theorem block409_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block409RightChunk000L : ℝ) (block409RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block409S1 : ℝ))
    (hy2ne : y ≠ (block409S2 : ℝ))
    (hy3ne : y ≠ (block409S3 : ℝ))
    (hy4ne : y ≠ (block409S4 : ℝ)) :
    0 < block409V y := by
  have hcert := block409RightChunk000Certificate_eq_true
  unfold block409RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block409RightChunk000) (lo := block409RightChunk000L) (hi := block409RightChunk000R)
    (w1 := block409W1) (w2 := block409W2) (w3 := block409W3) (w4 := block409W4)
    (s1 := block409S1) (s2 := block409S2) (s3 := block409S3) (s4 := block409S4)
    hboxes hcover block409RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block409RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block409RightChunk001 block409W1 block409W2 block409W3 block409W4 block409S1 block409S2 block409S3 block409S4

theorem block409RightChunk001ParamsCertificate_eq_true :
    block409RightChunk001ParamsCertificate = true := by
  native_decide

theorem block409_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block409RightChunk001L : ℝ) (block409RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block409S1 : ℝ))
    (hy2ne : y ≠ (block409S2 : ℝ))
    (hy3ne : y ≠ (block409S3 : ℝ))
    (hy4ne : y ≠ (block409S4 : ℝ)) :
    0 < block409V y := by
  have hcert := block409RightChunk001Certificate_eq_true
  unfold block409RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block409RightChunk001) (lo := block409RightChunk001L) (hi := block409RightChunk001R)
    (w1 := block409W1) (w2 := block409W2) (w3 := block409W3) (w4 := block409W4)
    (s1 := block409S1) (s2 := block409S2) (s3 := block409S3) (s4 := block409S4)
    hboxes hcover block409RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block409_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block409RightL : ℝ) (block409RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block409S1 : ℝ))
    (hy2ne : y ≠ (block409S2 : ℝ))
    (hy3ne : y ≠ (block409S3 : ℝ))
    (hy4ne : y ≠ (block409S4 : ℝ)) :
    0 < block409V y := by
  by_cases h0 : y ≤ (block409RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block409RightChunk000L : ℝ) (block409RightChunk000R : ℝ) := by
      have hL : (block409RightChunk000L : ℝ) = (block409RightL : ℝ) := by
        norm_num [block409RightChunk000L, block409RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block409_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block409RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block409RightChunk001L : ℝ) = (block409RightChunk000R : ℝ) := by
      norm_num [block409RightChunk001L, block409RightChunk000R]
    have hR : (block409RightChunk001R : ℝ) = (block409RightR : ℝ) := by
      norm_num [block409RightChunk001R, block409RightR]
    have hyc : y ∈ Icc (block409RightChunk001L : ℝ) (block409RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block409_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block409_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block409LeftL : ℝ) (block409LeftR : ℝ) →
    y ≠ 0 → y ≠ (block409S1 : ℝ) → y ≠ (block409S2 : ℝ) →
    y ≠ (block409S3 : ℝ) → y ≠ (block409S4 : ℝ) → 0 < block409V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block409RightL : ℝ) (block409RightR : ℝ) →
    y ≠ 0 → y ≠ (block409S1 : ℝ) → y ≠ (block409S2 : ℝ) →
    y ≠ (block409S3 : ℝ) → y ≠ (block409S4 : ℝ) → 0 < block409V y)

theorem block409_reallog_certificate_proof :
    block409_reallog_certificate := by
  exact ⟨block409_left_V_pos, block409_right_V_pos⟩

end Block409
end M1817475
end Erdos1038Lean
