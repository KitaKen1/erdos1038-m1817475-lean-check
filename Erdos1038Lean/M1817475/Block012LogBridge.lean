import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block012

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block012

open Set

def block012W1 : Rat := ((1119787590785889 : Rat) / 125000000000000)
def block012W2 : Rat := (0 : Rat)
def block012W3 : Rat := (0 : Rat)
def block012W4 : Rat := ((1269660112738711 : Rat) / 5000000000000000)
def block012S1 : Rat := ((18174751 : Rat) / 10000000)
def block012S2 : Rat := ((511587 : Rat) / 200000)
def block012S3 : Rat := ((107000619 : Rat) / 40000000)
def block012S4 : Rat := ((3539260540178571301 : Rat) / 1250000000000000000)

noncomputable def block012V (y : ℝ) : ℝ :=
  ratPotential block012W1 block012W2 block012W3 block012W4 block012S1 block012S2 block012S3 block012S4 y

def block012LeftParamsCertificate : Bool :=
  allBoxesSameParams block012LeftBoxes block012W1 block012W2 block012W3 block012W4 block012S1 block012S2 block012S3 block012S4

theorem block012LeftParamsCertificate_eq_true :
    block012LeftParamsCertificate = true := by
  native_decide

theorem block012_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block012LeftL : ℝ) (block012LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block012S1 : ℝ))
    (hy2ne : y ≠ (block012S2 : ℝ))
    (hy3ne : y ≠ (block012S3 : ℝ))
    (hy4ne : y ≠ (block012S4 : ℝ)) :
    0 < block012V y := by
  have hcert := block012LeftCertificate_eq_true
  unfold block012LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block012LeftBoxes) (lo := block012LeftL) (hi := block012LeftR)
    (w1 := block012W1) (w2 := block012W2) (w3 := block012W3) (w4 := block012W4)
    (s1 := block012S1) (s2 := block012S2) (s3 := block012S3) (s4 := block012S4)
    hboxes hcover block012LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block012RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block012RightChunk000 block012W1 block012W2 block012W3 block012W4 block012S1 block012S2 block012S3 block012S4

theorem block012RightChunk000ParamsCertificate_eq_true :
    block012RightChunk000ParamsCertificate = true := by
  native_decide

theorem block012_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block012RightChunk000L : ℝ) (block012RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block012S1 : ℝ))
    (hy2ne : y ≠ (block012S2 : ℝ))
    (hy3ne : y ≠ (block012S3 : ℝ))
    (hy4ne : y ≠ (block012S4 : ℝ)) :
    0 < block012V y := by
  have hcert := block012RightChunk000Certificate_eq_true
  unfold block012RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block012RightChunk000) (lo := block012RightChunk000L) (hi := block012RightChunk000R)
    (w1 := block012W1) (w2 := block012W2) (w3 := block012W3) (w4 := block012W4)
    (s1 := block012S1) (s2 := block012S2) (s3 := block012S3) (s4 := block012S4)
    hboxes hcover block012RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block012_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block012RightL : ℝ) (block012RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block012S1 : ℝ))
    (hy2ne : y ≠ (block012S2 : ℝ))
    (hy3ne : y ≠ (block012S3 : ℝ))
    (hy4ne : y ≠ (block012S4 : ℝ)) :
    0 < block012V y := by
  have hL : (block012RightChunk000L : ℝ) = (block012RightL : ℝ) := by
    norm_num [block012RightChunk000L, block012RightL]
  have hR : (block012RightChunk000R : ℝ) = (block012RightR : ℝ) := by
    norm_num [block012RightChunk000R, block012RightR]
  have hyc : y ∈ Icc (block012RightChunk000L : ℝ) (block012RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block012_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block012_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block012LeftL : ℝ) (block012LeftR : ℝ) →
    y ≠ 0 → y ≠ (block012S1 : ℝ) → y ≠ (block012S2 : ℝ) →
    y ≠ (block012S3 : ℝ) → y ≠ (block012S4 : ℝ) → 0 < block012V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block012RightL : ℝ) (block012RightR : ℝ) →
    y ≠ 0 → y ≠ (block012S1 : ℝ) → y ≠ (block012S2 : ℝ) →
    y ≠ (block012S3 : ℝ) → y ≠ (block012S4 : ℝ) → 0 < block012V y)

theorem block012_reallog_certificate_proof :
    block012_reallog_certificate := by
  exact ⟨block012_left_V_pos, block012_right_V_pos⟩

end Block012
end M1817475
end Erdos1038Lean
