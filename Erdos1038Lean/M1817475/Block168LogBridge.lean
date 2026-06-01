import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block168

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block168

open Set

def block168W1 : Rat := ((1831669565298327 : Rat) / 1000000000000000)
def block168W2 : Rat := (0 : Rat)
def block168W3 : Rat := ((8316651396275629 : Rat) / 50000000000000000)
def block168W4 : Rat := ((2043458617269471 : Rat) / 20000000000000000)
def block168S1 : Rat := ((18174751 : Rat) / 10000000)
def block168S2 : Rat := ((511587 : Rat) / 200000)
def block168S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block168S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block168V (y : ℝ) : ℝ :=
  ratPotential block168W1 block168W2 block168W3 block168W4 block168S1 block168S2 block168S3 block168S4 y

def block168LeftParamsCertificate : Bool :=
  allBoxesSameParams block168LeftBoxes block168W1 block168W2 block168W3 block168W4 block168S1 block168S2 block168S3 block168S4

theorem block168LeftParamsCertificate_eq_true :
    block168LeftParamsCertificate = true := by
  native_decide

theorem block168_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block168LeftL : ℝ) (block168LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block168S1 : ℝ))
    (hy2ne : y ≠ (block168S2 : ℝ))
    (hy3ne : y ≠ (block168S3 : ℝ))
    (hy4ne : y ≠ (block168S4 : ℝ)) :
    0 < block168V y := by
  have hcert := block168LeftCertificate_eq_true
  unfold block168LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block168LeftBoxes) (lo := block168LeftL) (hi := block168LeftR)
    (w1 := block168W1) (w2 := block168W2) (w3 := block168W3) (w4 := block168W4)
    (s1 := block168S1) (s2 := block168S2) (s3 := block168S3) (s4 := block168S4)
    hboxes hcover block168LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block168RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block168RightChunk000 block168W1 block168W2 block168W3 block168W4 block168S1 block168S2 block168S3 block168S4

theorem block168RightChunk000ParamsCertificate_eq_true :
    block168RightChunk000ParamsCertificate = true := by
  native_decide

theorem block168_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block168RightChunk000L : ℝ) (block168RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block168S1 : ℝ))
    (hy2ne : y ≠ (block168S2 : ℝ))
    (hy3ne : y ≠ (block168S3 : ℝ))
    (hy4ne : y ≠ (block168S4 : ℝ)) :
    0 < block168V y := by
  have hcert := block168RightChunk000Certificate_eq_true
  unfold block168RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block168RightChunk000) (lo := block168RightChunk000L) (hi := block168RightChunk000R)
    (w1 := block168W1) (w2 := block168W2) (w3 := block168W3) (w4 := block168W4)
    (s1 := block168S1) (s2 := block168S2) (s3 := block168S3) (s4 := block168S4)
    hboxes hcover block168RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block168RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block168RightChunk001 block168W1 block168W2 block168W3 block168W4 block168S1 block168S2 block168S3 block168S4

theorem block168RightChunk001ParamsCertificate_eq_true :
    block168RightChunk001ParamsCertificate = true := by
  native_decide

theorem block168_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block168RightChunk001L : ℝ) (block168RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block168S1 : ℝ))
    (hy2ne : y ≠ (block168S2 : ℝ))
    (hy3ne : y ≠ (block168S3 : ℝ))
    (hy4ne : y ≠ (block168S4 : ℝ)) :
    0 < block168V y := by
  have hcert := block168RightChunk001Certificate_eq_true
  unfold block168RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block168RightChunk001) (lo := block168RightChunk001L) (hi := block168RightChunk001R)
    (w1 := block168W1) (w2 := block168W2) (w3 := block168W3) (w4 := block168W4)
    (s1 := block168S1) (s2 := block168S2) (s3 := block168S3) (s4 := block168S4)
    hboxes hcover block168RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block168_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block168RightL : ℝ) (block168RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block168S1 : ℝ))
    (hy2ne : y ≠ (block168S2 : ℝ))
    (hy3ne : y ≠ (block168S3 : ℝ))
    (hy4ne : y ≠ (block168S4 : ℝ)) :
    0 < block168V y := by
  by_cases h0 : y ≤ (block168RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block168RightChunk000L : ℝ) (block168RightChunk000R : ℝ) := by
      have hL : (block168RightChunk000L : ℝ) = (block168RightL : ℝ) := by
        norm_num [block168RightChunk000L, block168RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block168_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block168RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block168RightChunk001L : ℝ) = (block168RightChunk000R : ℝ) := by
      norm_num [block168RightChunk001L, block168RightChunk000R]
    have hR : (block168RightChunk001R : ℝ) = (block168RightR : ℝ) := by
      norm_num [block168RightChunk001R, block168RightR]
    have hyc : y ∈ Icc (block168RightChunk001L : ℝ) (block168RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block168_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block168_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block168LeftL : ℝ) (block168LeftR : ℝ) →
    y ≠ 0 → y ≠ (block168S1 : ℝ) → y ≠ (block168S2 : ℝ) →
    y ≠ (block168S3 : ℝ) → y ≠ (block168S4 : ℝ) → 0 < block168V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block168RightL : ℝ) (block168RightR : ℝ) →
    y ≠ 0 → y ≠ (block168S1 : ℝ) → y ≠ (block168S2 : ℝ) →
    y ≠ (block168S3 : ℝ) → y ≠ (block168S4 : ℝ) → 0 < block168V y)

theorem block168_reallog_certificate_proof :
    block168_reallog_certificate := by
  exact ⟨block168_left_V_pos, block168_right_V_pos⟩

end Block168
end M1817475
end Erdos1038Lean
