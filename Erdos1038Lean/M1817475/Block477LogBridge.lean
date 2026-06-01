import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block477

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block477

open Set

def block477W1 : Rat := ((1306067705967317 : Rat) / 2500000000000000)
def block477W2 : Rat := (0 : Rat)
def block477W3 : Rat := ((18665690572969787 : Rat) / 50000000000000000)
def block477W4 : Rat := ((1121373553156173 : Rat) / 25000000000000000)
def block477S1 : Rat := ((18174751 : Rat) / 10000000)
def block477S2 : Rat := ((511587 : Rat) / 200000)
def block477S3 : Rat := ((130808633125000000129 : Rat) / 50000000000000000000)
def block477S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block477V (y : ℝ) : ℝ :=
  ratPotential block477W1 block477W2 block477W3 block477W4 block477S1 block477S2 block477S3 block477S4 y

def block477LeftParamsCertificate : Bool :=
  allBoxesSameParams block477LeftBoxes block477W1 block477W2 block477W3 block477W4 block477S1 block477S2 block477S3 block477S4

theorem block477LeftParamsCertificate_eq_true :
    block477LeftParamsCertificate = true := by
  native_decide

theorem block477_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block477LeftL : ℝ) (block477LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block477S1 : ℝ))
    (hy2ne : y ≠ (block477S2 : ℝ))
    (hy3ne : y ≠ (block477S3 : ℝ))
    (hy4ne : y ≠ (block477S4 : ℝ)) :
    0 < block477V y := by
  have hcert := block477LeftCertificate_eq_true
  unfold block477LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block477LeftBoxes) (lo := block477LeftL) (hi := block477LeftR)
    (w1 := block477W1) (w2 := block477W2) (w3 := block477W3) (w4 := block477W4)
    (s1 := block477S1) (s2 := block477S2) (s3 := block477S3) (s4 := block477S4)
    hboxes hcover block477LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block477RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block477RightChunk000 block477W1 block477W2 block477W3 block477W4 block477S1 block477S2 block477S3 block477S4

theorem block477RightChunk000ParamsCertificate_eq_true :
    block477RightChunk000ParamsCertificate = true := by
  native_decide

theorem block477_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block477RightChunk000L : ℝ) (block477RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block477S1 : ℝ))
    (hy2ne : y ≠ (block477S2 : ℝ))
    (hy3ne : y ≠ (block477S3 : ℝ))
    (hy4ne : y ≠ (block477S4 : ℝ)) :
    0 < block477V y := by
  have hcert := block477RightChunk000Certificate_eq_true
  unfold block477RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block477RightChunk000) (lo := block477RightChunk000L) (hi := block477RightChunk000R)
    (w1 := block477W1) (w2 := block477W2) (w3 := block477W3) (w4 := block477W4)
    (s1 := block477S1) (s2 := block477S2) (s3 := block477S3) (s4 := block477S4)
    hboxes hcover block477RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block477_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block477RightL : ℝ) (block477RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block477S1 : ℝ))
    (hy2ne : y ≠ (block477S2 : ℝ))
    (hy3ne : y ≠ (block477S3 : ℝ))
    (hy4ne : y ≠ (block477S4 : ℝ)) :
    0 < block477V y := by
  have hL : (block477RightChunk000L : ℝ) = (block477RightL : ℝ) := by
    norm_num [block477RightChunk000L, block477RightL]
  have hR : (block477RightChunk000R : ℝ) = (block477RightR : ℝ) := by
    norm_num [block477RightChunk000R, block477RightR]
  have hyc : y ∈ Icc (block477RightChunk000L : ℝ) (block477RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block477_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block477_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block477LeftL : ℝ) (block477LeftR : ℝ) →
    y ≠ 0 → y ≠ (block477S1 : ℝ) → y ≠ (block477S2 : ℝ) →
    y ≠ (block477S3 : ℝ) → y ≠ (block477S4 : ℝ) → 0 < block477V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block477RightL : ℝ) (block477RightR : ℝ) →
    y ≠ 0 → y ≠ (block477S1 : ℝ) → y ≠ (block477S2 : ℝ) →
    y ≠ (block477S3 : ℝ) → y ≠ (block477S4 : ℝ) → 0 < block477V y)

theorem block477_reallog_certificate_proof :
    block477_reallog_certificate := by
  exact ⟨block477_left_V_pos, block477_right_V_pos⟩

end Block477
end M1817475
end Erdos1038Lean
