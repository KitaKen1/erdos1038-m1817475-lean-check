import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block148

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block148

open Set

def block148W1 : Rat := ((5624651472118679 : Rat) / 2500000000000000)
def block148W2 : Rat := (0 : Rat)
def block148W3 : Rat := ((1576177149234017 : Rat) / 10000000000000000)
def block148W4 : Rat := ((4566305190884993 : Rat) / 50000000000000000)
def block148S1 : Rat := ((18174751 : Rat) / 10000000)
def block148S2 : Rat := ((511587 : Rat) / 200000)
def block148S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block148S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block148V (y : ℝ) : ℝ :=
  ratPotential block148W1 block148W2 block148W3 block148W4 block148S1 block148S2 block148S3 block148S4 y

def block148LeftParamsCertificate : Bool :=
  allBoxesSameParams block148LeftBoxes block148W1 block148W2 block148W3 block148W4 block148S1 block148S2 block148S3 block148S4

theorem block148LeftParamsCertificate_eq_true :
    block148LeftParamsCertificate = true := by
  native_decide

theorem block148_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block148LeftL : ℝ) (block148LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block148S1 : ℝ))
    (hy2ne : y ≠ (block148S2 : ℝ))
    (hy3ne : y ≠ (block148S3 : ℝ))
    (hy4ne : y ≠ (block148S4 : ℝ)) :
    0 < block148V y := by
  have hcert := block148LeftCertificate_eq_true
  unfold block148LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block148LeftBoxes) (lo := block148LeftL) (hi := block148LeftR)
    (w1 := block148W1) (w2 := block148W2) (w3 := block148W3) (w4 := block148W4)
    (s1 := block148S1) (s2 := block148S2) (s3 := block148S3) (s4 := block148S4)
    hboxes hcover block148LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block148RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block148RightChunk000 block148W1 block148W2 block148W3 block148W4 block148S1 block148S2 block148S3 block148S4

theorem block148RightChunk000ParamsCertificate_eq_true :
    block148RightChunk000ParamsCertificate = true := by
  native_decide

theorem block148_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block148RightChunk000L : ℝ) (block148RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block148S1 : ℝ))
    (hy2ne : y ≠ (block148S2 : ℝ))
    (hy3ne : y ≠ (block148S3 : ℝ))
    (hy4ne : y ≠ (block148S4 : ℝ)) :
    0 < block148V y := by
  have hcert := block148RightChunk000Certificate_eq_true
  unfold block148RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block148RightChunk000) (lo := block148RightChunk000L) (hi := block148RightChunk000R)
    (w1 := block148W1) (w2 := block148W2) (w3 := block148W3) (w4 := block148W4)
    (s1 := block148S1) (s2 := block148S2) (s3 := block148S3) (s4 := block148S4)
    hboxes hcover block148RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block148_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block148RightL : ℝ) (block148RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block148S1 : ℝ))
    (hy2ne : y ≠ (block148S2 : ℝ))
    (hy3ne : y ≠ (block148S3 : ℝ))
    (hy4ne : y ≠ (block148S4 : ℝ)) :
    0 < block148V y := by
  have hL : (block148RightChunk000L : ℝ) = (block148RightL : ℝ) := by
    norm_num [block148RightChunk000L, block148RightL]
  have hR : (block148RightChunk000R : ℝ) = (block148RightR : ℝ) := by
    norm_num [block148RightChunk000R, block148RightR]
  have hyc : y ∈ Icc (block148RightChunk000L : ℝ) (block148RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block148_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block148_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block148LeftL : ℝ) (block148LeftR : ℝ) →
    y ≠ 0 → y ≠ (block148S1 : ℝ) → y ≠ (block148S2 : ℝ) →
    y ≠ (block148S3 : ℝ) → y ≠ (block148S4 : ℝ) → 0 < block148V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block148RightL : ℝ) (block148RightR : ℝ) →
    y ≠ 0 → y ≠ (block148S1 : ℝ) → y ≠ (block148S2 : ℝ) →
    y ≠ (block148S3 : ℝ) → y ≠ (block148S4 : ℝ) → 0 < block148V y)

theorem block148_reallog_certificate_proof :
    block148_reallog_certificate := by
  exact ⟨block148_left_V_pos, block148_right_V_pos⟩

end Block148
end M1817475
end Erdos1038Lean
