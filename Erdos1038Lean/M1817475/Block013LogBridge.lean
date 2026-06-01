import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block013

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block013

open Set

def block013W1 : Rat := ((4342612687605687 : Rat) / 500000000000000)
def block013W2 : Rat := (0 : Rat)
def block013W3 : Rat := (0 : Rat)
def block013W4 : Rat := ((12730352082081897 : Rat) / 50000000000000000)
def block013S1 : Rat := ((18174751 : Rat) / 10000000)
def block013S2 : Rat := ((511587 : Rat) / 200000)
def block013S3 : Rat := ((107000619 : Rat) / 40000000)
def block013S4 : Rat := ((3539260540178571301 : Rat) / 1250000000000000000)

noncomputable def block013V (y : ℝ) : ℝ :=
  ratPotential block013W1 block013W2 block013W3 block013W4 block013S1 block013S2 block013S3 block013S4 y

def block013LeftParamsCertificate : Bool :=
  allBoxesSameParams block013LeftBoxes block013W1 block013W2 block013W3 block013W4 block013S1 block013S2 block013S3 block013S4

theorem block013LeftParamsCertificate_eq_true :
    block013LeftParamsCertificate = true := by
  native_decide

theorem block013_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block013LeftL : ℝ) (block013LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block013S1 : ℝ))
    (hy2ne : y ≠ (block013S2 : ℝ))
    (hy3ne : y ≠ (block013S3 : ℝ))
    (hy4ne : y ≠ (block013S4 : ℝ)) :
    0 < block013V y := by
  have hcert := block013LeftCertificate_eq_true
  unfold block013LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block013LeftBoxes) (lo := block013LeftL) (hi := block013LeftR)
    (w1 := block013W1) (w2 := block013W2) (w3 := block013W3) (w4 := block013W4)
    (s1 := block013S1) (s2 := block013S2) (s3 := block013S3) (s4 := block013S4)
    hboxes hcover block013LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block013RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block013RightChunk000 block013W1 block013W2 block013W3 block013W4 block013S1 block013S2 block013S3 block013S4

theorem block013RightChunk000ParamsCertificate_eq_true :
    block013RightChunk000ParamsCertificate = true := by
  native_decide

theorem block013_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block013RightChunk000L : ℝ) (block013RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block013S1 : ℝ))
    (hy2ne : y ≠ (block013S2 : ℝ))
    (hy3ne : y ≠ (block013S3 : ℝ))
    (hy4ne : y ≠ (block013S4 : ℝ)) :
    0 < block013V y := by
  have hcert := block013RightChunk000Certificate_eq_true
  unfold block013RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block013RightChunk000) (lo := block013RightChunk000L) (hi := block013RightChunk000R)
    (w1 := block013W1) (w2 := block013W2) (w3 := block013W3) (w4 := block013W4)
    (s1 := block013S1) (s2 := block013S2) (s3 := block013S3) (s4 := block013S4)
    hboxes hcover block013RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block013_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block013RightL : ℝ) (block013RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block013S1 : ℝ))
    (hy2ne : y ≠ (block013S2 : ℝ))
    (hy3ne : y ≠ (block013S3 : ℝ))
    (hy4ne : y ≠ (block013S4 : ℝ)) :
    0 < block013V y := by
  have hL : (block013RightChunk000L : ℝ) = (block013RightL : ℝ) := by
    norm_num [block013RightChunk000L, block013RightL]
  have hR : (block013RightChunk000R : ℝ) = (block013RightR : ℝ) := by
    norm_num [block013RightChunk000R, block013RightR]
  have hyc : y ∈ Icc (block013RightChunk000L : ℝ) (block013RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block013_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block013_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block013LeftL : ℝ) (block013LeftR : ℝ) →
    y ≠ 0 → y ≠ (block013S1 : ℝ) → y ≠ (block013S2 : ℝ) →
    y ≠ (block013S3 : ℝ) → y ≠ (block013S4 : ℝ) → 0 < block013V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block013RightL : ℝ) (block013RightR : ℝ) →
    y ≠ 0 → y ≠ (block013S1 : ℝ) → y ≠ (block013S2 : ℝ) →
    y ≠ (block013S3 : ℝ) → y ≠ (block013S4 : ℝ) → 0 < block013V y)

theorem block013_reallog_certificate_proof :
    block013_reallog_certificate := by
  exact ⟨block013_left_V_pos, block013_right_V_pos⟩

end Block013
end M1817475
end Erdos1038Lean
