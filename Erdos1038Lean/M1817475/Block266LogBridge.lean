import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block266

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block266

open Set

def block266W1 : Rat := ((2572133444579613 : Rat) / 2500000000000000)
def block266W2 : Rat := ((1712554528473291 : Rat) / 62500000000000000)
def block266W3 : Rat := ((29565097464078177 : Rat) / 100000000000000000)
def block266W4 : Rat := (0 : Rat)
def block266S1 : Rat := ((18174751 : Rat) / 10000000)
def block266S2 : Rat := ((511587 : Rat) / 200000)
def block266S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block266S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block266V (y : ℝ) : ℝ :=
  ratPotential block266W1 block266W2 block266W3 block266W4 block266S1 block266S2 block266S3 block266S4 y

def block266LeftParamsCertificate : Bool :=
  allBoxesSameParams block266LeftBoxes block266W1 block266W2 block266W3 block266W4 block266S1 block266S2 block266S3 block266S4

theorem block266LeftParamsCertificate_eq_true :
    block266LeftParamsCertificate = true := by
  native_decide

theorem block266_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block266LeftL : ℝ) (block266LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block266S1 : ℝ))
    (hy2ne : y ≠ (block266S2 : ℝ))
    (hy3ne : y ≠ (block266S3 : ℝ))
    (hy4ne : y ≠ (block266S4 : ℝ)) :
    0 < block266V y := by
  have hcert := block266LeftCertificate_eq_true
  unfold block266LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block266LeftBoxes) (lo := block266LeftL) (hi := block266LeftR)
    (w1 := block266W1) (w2 := block266W2) (w3 := block266W3) (w4 := block266W4)
    (s1 := block266S1) (s2 := block266S2) (s3 := block266S3) (s4 := block266S4)
    hboxes hcover block266LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block266RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block266RightChunk000 block266W1 block266W2 block266W3 block266W4 block266S1 block266S2 block266S3 block266S4

theorem block266RightChunk000ParamsCertificate_eq_true :
    block266RightChunk000ParamsCertificate = true := by
  native_decide

theorem block266_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block266RightChunk000L : ℝ) (block266RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block266S1 : ℝ))
    (hy2ne : y ≠ (block266S2 : ℝ))
    (hy3ne : y ≠ (block266S3 : ℝ))
    (hy4ne : y ≠ (block266S4 : ℝ)) :
    0 < block266V y := by
  have hcert := block266RightChunk000Certificate_eq_true
  unfold block266RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block266RightChunk000) (lo := block266RightChunk000L) (hi := block266RightChunk000R)
    (w1 := block266W1) (w2 := block266W2) (w3 := block266W3) (w4 := block266W4)
    (s1 := block266S1) (s2 := block266S2) (s3 := block266S3) (s4 := block266S4)
    hboxes hcover block266RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block266RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block266RightChunk001 block266W1 block266W2 block266W3 block266W4 block266S1 block266S2 block266S3 block266S4

theorem block266RightChunk001ParamsCertificate_eq_true :
    block266RightChunk001ParamsCertificate = true := by
  native_decide

theorem block266_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block266RightChunk001L : ℝ) (block266RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block266S1 : ℝ))
    (hy2ne : y ≠ (block266S2 : ℝ))
    (hy3ne : y ≠ (block266S3 : ℝ))
    (hy4ne : y ≠ (block266S4 : ℝ)) :
    0 < block266V y := by
  have hcert := block266RightChunk001Certificate_eq_true
  unfold block266RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block266RightChunk001) (lo := block266RightChunk001L) (hi := block266RightChunk001R)
    (w1 := block266W1) (w2 := block266W2) (w3 := block266W3) (w4 := block266W4)
    (s1 := block266S1) (s2 := block266S2) (s3 := block266S3) (s4 := block266S4)
    hboxes hcover block266RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block266_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block266RightL : ℝ) (block266RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block266S1 : ℝ))
    (hy2ne : y ≠ (block266S2 : ℝ))
    (hy3ne : y ≠ (block266S3 : ℝ))
    (hy4ne : y ≠ (block266S4 : ℝ)) :
    0 < block266V y := by
  by_cases h0 : y ≤ (block266RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block266RightChunk000L : ℝ) (block266RightChunk000R : ℝ) := by
      have hL : (block266RightChunk000L : ℝ) = (block266RightL : ℝ) := by
        norm_num [block266RightChunk000L, block266RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block266_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block266RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block266RightChunk001L : ℝ) = (block266RightChunk000R : ℝ) := by
      norm_num [block266RightChunk001L, block266RightChunk000R]
    have hR : (block266RightChunk001R : ℝ) = (block266RightR : ℝ) := by
      norm_num [block266RightChunk001R, block266RightR]
    have hyc : y ∈ Icc (block266RightChunk001L : ℝ) (block266RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block266_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block266_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block266LeftL : ℝ) (block266LeftR : ℝ) →
    y ≠ 0 → y ≠ (block266S1 : ℝ) → y ≠ (block266S2 : ℝ) →
    y ≠ (block266S3 : ℝ) → y ≠ (block266S4 : ℝ) → 0 < block266V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block266RightL : ℝ) (block266RightR : ℝ) →
    y ≠ 0 → y ≠ (block266S1 : ℝ) → y ≠ (block266S2 : ℝ) →
    y ≠ (block266S3 : ℝ) → y ≠ (block266S4 : ℝ) → 0 < block266V y)

theorem block266_reallog_certificate_proof :
    block266_reallog_certificate := by
  exact ⟨block266_left_V_pos, block266_right_V_pos⟩

end Block266
end M1817475
end Erdos1038Lean
