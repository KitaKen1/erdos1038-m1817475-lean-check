import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block138

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block138

open Set

def block138W1 : Rat := ((5047462347975249 : Rat) / 2000000000000000)
def block138W2 : Rat := (0 : Rat)
def block138W3 : Rat := ((11879327299912469 : Rat) / 100000000000000000)
def block138W4 : Rat := ((1512277215407613 : Rat) / 12500000000000000)
def block138S1 : Rat := ((18174751 : Rat) / 10000000)
def block138S2 : Rat := ((511587 : Rat) / 200000)
def block138S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block138S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block138V (y : ℝ) : ℝ :=
  ratPotential block138W1 block138W2 block138W3 block138W4 block138S1 block138S2 block138S3 block138S4 y

def block138LeftParamsCertificate : Bool :=
  allBoxesSameParams block138LeftBoxes block138W1 block138W2 block138W3 block138W4 block138S1 block138S2 block138S3 block138S4

theorem block138LeftParamsCertificate_eq_true :
    block138LeftParamsCertificate = true := by
  native_decide

theorem block138_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block138LeftL : ℝ) (block138LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block138S1 : ℝ))
    (hy2ne : y ≠ (block138S2 : ℝ))
    (hy3ne : y ≠ (block138S3 : ℝ))
    (hy4ne : y ≠ (block138S4 : ℝ)) :
    0 < block138V y := by
  have hcert := block138LeftCertificate_eq_true
  unfold block138LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block138LeftBoxes) (lo := block138LeftL) (hi := block138LeftR)
    (w1 := block138W1) (w2 := block138W2) (w3 := block138W3) (w4 := block138W4)
    (s1 := block138S1) (s2 := block138S2) (s3 := block138S3) (s4 := block138S4)
    hboxes hcover block138LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block138RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block138RightChunk000 block138W1 block138W2 block138W3 block138W4 block138S1 block138S2 block138S3 block138S4

theorem block138RightChunk000ParamsCertificate_eq_true :
    block138RightChunk000ParamsCertificate = true := by
  native_decide

theorem block138_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block138RightChunk000L : ℝ) (block138RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block138S1 : ℝ))
    (hy2ne : y ≠ (block138S2 : ℝ))
    (hy3ne : y ≠ (block138S3 : ℝ))
    (hy4ne : y ≠ (block138S4 : ℝ)) :
    0 < block138V y := by
  have hcert := block138RightChunk000Certificate_eq_true
  unfold block138RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block138RightChunk000) (lo := block138RightChunk000L) (hi := block138RightChunk000R)
    (w1 := block138W1) (w2 := block138W2) (w3 := block138W3) (w4 := block138W4)
    (s1 := block138S1) (s2 := block138S2) (s3 := block138S3) (s4 := block138S4)
    hboxes hcover block138RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block138_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block138RightL : ℝ) (block138RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block138S1 : ℝ))
    (hy2ne : y ≠ (block138S2 : ℝ))
    (hy3ne : y ≠ (block138S3 : ℝ))
    (hy4ne : y ≠ (block138S4 : ℝ)) :
    0 < block138V y := by
  have hL : (block138RightChunk000L : ℝ) = (block138RightL : ℝ) := by
    norm_num [block138RightChunk000L, block138RightL]
  have hR : (block138RightChunk000R : ℝ) = (block138RightR : ℝ) := by
    norm_num [block138RightChunk000R, block138RightR]
  have hyc : y ∈ Icc (block138RightChunk000L : ℝ) (block138RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block138_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block138_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block138LeftL : ℝ) (block138LeftR : ℝ) →
    y ≠ 0 → y ≠ (block138S1 : ℝ) → y ≠ (block138S2 : ℝ) →
    y ≠ (block138S3 : ℝ) → y ≠ (block138S4 : ℝ) → 0 < block138V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block138RightL : ℝ) (block138RightR : ℝ) →
    y ≠ 0 → y ≠ (block138S1 : ℝ) → y ≠ (block138S2 : ℝ) →
    y ≠ (block138S3 : ℝ) → y ≠ (block138S4 : ℝ) → 0 < block138V y)

theorem block138_reallog_certificate_proof :
    block138_reallog_certificate := by
  exact ⟨block138_left_V_pos, block138_right_V_pos⟩

end Block138
end M1817475
end Erdos1038Lean
