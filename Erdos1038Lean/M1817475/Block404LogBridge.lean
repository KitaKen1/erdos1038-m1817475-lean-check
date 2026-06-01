import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block404

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block404

open Set

def block404W1 : Rat := ((737633183312251 : Rat) / 1000000000000000)
def block404W2 : Rat := (0 : Rat)
def block404W3 : Rat := ((2803312549968369 : Rat) / 10000000000000000)
def block404W4 : Rat := ((36832527822123 : Rat) / 400000000000000)
def block404S1 : Rat := ((18174751 : Rat) / 10000000)
def block404S2 : Rat := ((511587 : Rat) / 200000)
def block404S3 : Rat := ((26447143589285714299 : Rat) / 10000000000000000000)
def block404S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block404V (y : ℝ) : ℝ :=
  ratPotential block404W1 block404W2 block404W3 block404W4 block404S1 block404S2 block404S3 block404S4 y

def block404LeftParamsCertificate : Bool :=
  allBoxesSameParams block404LeftBoxes block404W1 block404W2 block404W3 block404W4 block404S1 block404S2 block404S3 block404S4

theorem block404LeftParamsCertificate_eq_true :
    block404LeftParamsCertificate = true := by
  native_decide

theorem block404_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block404LeftL : ℝ) (block404LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block404S1 : ℝ))
    (hy2ne : y ≠ (block404S2 : ℝ))
    (hy3ne : y ≠ (block404S3 : ℝ))
    (hy4ne : y ≠ (block404S4 : ℝ)) :
    0 < block404V y := by
  have hcert := block404LeftCertificate_eq_true
  unfold block404LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block404LeftBoxes) (lo := block404LeftL) (hi := block404LeftR)
    (w1 := block404W1) (w2 := block404W2) (w3 := block404W3) (w4 := block404W4)
    (s1 := block404S1) (s2 := block404S2) (s3 := block404S3) (s4 := block404S4)
    hboxes hcover block404LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block404RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block404RightChunk000 block404W1 block404W2 block404W3 block404W4 block404S1 block404S2 block404S3 block404S4

theorem block404RightChunk000ParamsCertificate_eq_true :
    block404RightChunk000ParamsCertificate = true := by
  native_decide

theorem block404_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block404RightChunk000L : ℝ) (block404RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block404S1 : ℝ))
    (hy2ne : y ≠ (block404S2 : ℝ))
    (hy3ne : y ≠ (block404S3 : ℝ))
    (hy4ne : y ≠ (block404S4 : ℝ)) :
    0 < block404V y := by
  have hcert := block404RightChunk000Certificate_eq_true
  unfold block404RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block404RightChunk000) (lo := block404RightChunk000L) (hi := block404RightChunk000R)
    (w1 := block404W1) (w2 := block404W2) (w3 := block404W3) (w4 := block404W4)
    (s1 := block404S1) (s2 := block404S2) (s3 := block404S3) (s4 := block404S4)
    hboxes hcover block404RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block404RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block404RightChunk001 block404W1 block404W2 block404W3 block404W4 block404S1 block404S2 block404S3 block404S4

theorem block404RightChunk001ParamsCertificate_eq_true :
    block404RightChunk001ParamsCertificate = true := by
  native_decide

theorem block404_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block404RightChunk001L : ℝ) (block404RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block404S1 : ℝ))
    (hy2ne : y ≠ (block404S2 : ℝ))
    (hy3ne : y ≠ (block404S3 : ℝ))
    (hy4ne : y ≠ (block404S4 : ℝ)) :
    0 < block404V y := by
  have hcert := block404RightChunk001Certificate_eq_true
  unfold block404RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block404RightChunk001) (lo := block404RightChunk001L) (hi := block404RightChunk001R)
    (w1 := block404W1) (w2 := block404W2) (w3 := block404W3) (w4 := block404W4)
    (s1 := block404S1) (s2 := block404S2) (s3 := block404S3) (s4 := block404S4)
    hboxes hcover block404RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block404_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block404RightL : ℝ) (block404RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block404S1 : ℝ))
    (hy2ne : y ≠ (block404S2 : ℝ))
    (hy3ne : y ≠ (block404S3 : ℝ))
    (hy4ne : y ≠ (block404S4 : ℝ)) :
    0 < block404V y := by
  by_cases h0 : y ≤ (block404RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block404RightChunk000L : ℝ) (block404RightChunk000R : ℝ) := by
      have hL : (block404RightChunk000L : ℝ) = (block404RightL : ℝ) := by
        norm_num [block404RightChunk000L, block404RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block404_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block404RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block404RightChunk001L : ℝ) = (block404RightChunk000R : ℝ) := by
      norm_num [block404RightChunk001L, block404RightChunk000R]
    have hR : (block404RightChunk001R : ℝ) = (block404RightR : ℝ) := by
      norm_num [block404RightChunk001R, block404RightR]
    have hyc : y ∈ Icc (block404RightChunk001L : ℝ) (block404RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block404_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block404_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block404LeftL : ℝ) (block404LeftR : ℝ) →
    y ≠ 0 → y ≠ (block404S1 : ℝ) → y ≠ (block404S2 : ℝ) →
    y ≠ (block404S3 : ℝ) → y ≠ (block404S4 : ℝ) → 0 < block404V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block404RightL : ℝ) (block404RightR : ℝ) →
    y ≠ 0 → y ≠ (block404S1 : ℝ) → y ≠ (block404S2 : ℝ) →
    y ≠ (block404S3 : ℝ) → y ≠ (block404S4 : ℝ) → 0 < block404V y)

theorem block404_reallog_certificate_proof :
    block404_reallog_certificate := by
  exact ⟨block404_left_V_pos, block404_right_V_pos⟩

end Block404
end M1817475
end Erdos1038Lean
