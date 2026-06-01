import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block427

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block427

open Set

def block427W1 : Rat := ((6653437703154239 : Rat) / 10000000000000000)
def block427W2 : Rat := (0 : Rat)
def block427W3 : Rat := ((3044960915289041 : Rat) / 10000000000000000)
def block427W4 : Rat := ((8140821568631947 : Rat) / 100000000000000000)
def block427S1 : Rat := ((18174751 : Rat) / 10000000)
def block427S2 : Rat := ((511587 : Rat) / 200000)
def block427S3 : Rat := ((131786088482142857229 : Rat) / 50000000000000000000)
def block427S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block427V (y : ℝ) : ℝ :=
  ratPotential block427W1 block427W2 block427W3 block427W4 block427S1 block427S2 block427S3 block427S4 y

def block427LeftParamsCertificate : Bool :=
  allBoxesSameParams block427LeftBoxes block427W1 block427W2 block427W3 block427W4 block427S1 block427S2 block427S3 block427S4

theorem block427LeftParamsCertificate_eq_true :
    block427LeftParamsCertificate = true := by
  native_decide

theorem block427_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block427LeftL : ℝ) (block427LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block427S1 : ℝ))
    (hy2ne : y ≠ (block427S2 : ℝ))
    (hy3ne : y ≠ (block427S3 : ℝ))
    (hy4ne : y ≠ (block427S4 : ℝ)) :
    0 < block427V y := by
  have hcert := block427LeftCertificate_eq_true
  unfold block427LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block427LeftBoxes) (lo := block427LeftL) (hi := block427LeftR)
    (w1 := block427W1) (w2 := block427W2) (w3 := block427W3) (w4 := block427W4)
    (s1 := block427S1) (s2 := block427S2) (s3 := block427S3) (s4 := block427S4)
    hboxes hcover block427LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block427RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block427RightChunk000 block427W1 block427W2 block427W3 block427W4 block427S1 block427S2 block427S3 block427S4

theorem block427RightChunk000ParamsCertificate_eq_true :
    block427RightChunk000ParamsCertificate = true := by
  native_decide

theorem block427_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block427RightChunk000L : ℝ) (block427RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block427S1 : ℝ))
    (hy2ne : y ≠ (block427S2 : ℝ))
    (hy3ne : y ≠ (block427S3 : ℝ))
    (hy4ne : y ≠ (block427S4 : ℝ)) :
    0 < block427V y := by
  have hcert := block427RightChunk000Certificate_eq_true
  unfold block427RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block427RightChunk000) (lo := block427RightChunk000L) (hi := block427RightChunk000R)
    (w1 := block427W1) (w2 := block427W2) (w3 := block427W3) (w4 := block427W4)
    (s1 := block427S1) (s2 := block427S2) (s3 := block427S3) (s4 := block427S4)
    hboxes hcover block427RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block427_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block427RightL : ℝ) (block427RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block427S1 : ℝ))
    (hy2ne : y ≠ (block427S2 : ℝ))
    (hy3ne : y ≠ (block427S3 : ℝ))
    (hy4ne : y ≠ (block427S4 : ℝ)) :
    0 < block427V y := by
  have hL : (block427RightChunk000L : ℝ) = (block427RightL : ℝ) := by
    norm_num [block427RightChunk000L, block427RightL]
  have hR : (block427RightChunk000R : ℝ) = (block427RightR : ℝ) := by
    norm_num [block427RightChunk000R, block427RightR]
  have hyc : y ∈ Icc (block427RightChunk000L : ℝ) (block427RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block427_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block427_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block427LeftL : ℝ) (block427LeftR : ℝ) →
    y ≠ 0 → y ≠ (block427S1 : ℝ) → y ≠ (block427S2 : ℝ) →
    y ≠ (block427S3 : ℝ) → y ≠ (block427S4 : ℝ) → 0 < block427V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block427RightL : ℝ) (block427RightR : ℝ) →
    y ≠ 0 → y ≠ (block427S1 : ℝ) → y ≠ (block427S2 : ℝ) →
    y ≠ (block427S3 : ℝ) → y ≠ (block427S4 : ℝ) → 0 < block427V y)

theorem block427_reallog_certificate_proof :
    block427_reallog_certificate := by
  exact ⟨block427_left_V_pos, block427_right_V_pos⟩

end Block427
end M1817475
end Erdos1038Lean
