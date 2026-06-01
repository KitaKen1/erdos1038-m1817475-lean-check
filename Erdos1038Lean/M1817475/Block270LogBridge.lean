import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block270

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block270

open Set

def block270W1 : Rat := ((10290353672535881 : Rat) / 10000000000000000)
def block270W2 : Rat := ((14524530791018099 : Rat) / 500000000000000000)
def block270W3 : Rat := ((732597724988143 : Rat) / 2500000000000000)
def block270W4 : Rat := (0 : Rat)
def block270S1 : Rat := ((18174751 : Rat) / 10000000)
def block270S2 : Rat := ((511587 : Rat) / 200000)
def block270S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block270S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block270V (y : ℝ) : ℝ :=
  ratPotential block270W1 block270W2 block270W3 block270W4 block270S1 block270S2 block270S3 block270S4 y

def block270LeftParamsCertificate : Bool :=
  allBoxesSameParams block270LeftBoxes block270W1 block270W2 block270W3 block270W4 block270S1 block270S2 block270S3 block270S4

theorem block270LeftParamsCertificate_eq_true :
    block270LeftParamsCertificate = true := by
  native_decide

theorem block270_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block270LeftL : ℝ) (block270LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block270S1 : ℝ))
    (hy2ne : y ≠ (block270S2 : ℝ))
    (hy3ne : y ≠ (block270S3 : ℝ))
    (hy4ne : y ≠ (block270S4 : ℝ)) :
    0 < block270V y := by
  have hcert := block270LeftCertificate_eq_true
  unfold block270LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block270LeftBoxes) (lo := block270LeftL) (hi := block270LeftR)
    (w1 := block270W1) (w2 := block270W2) (w3 := block270W3) (w4 := block270W4)
    (s1 := block270S1) (s2 := block270S2) (s3 := block270S3) (s4 := block270S4)
    hboxes hcover block270LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block270RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block270RightChunk000 block270W1 block270W2 block270W3 block270W4 block270S1 block270S2 block270S3 block270S4

theorem block270RightChunk000ParamsCertificate_eq_true :
    block270RightChunk000ParamsCertificate = true := by
  native_decide

theorem block270_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block270RightChunk000L : ℝ) (block270RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block270S1 : ℝ))
    (hy2ne : y ≠ (block270S2 : ℝ))
    (hy3ne : y ≠ (block270S3 : ℝ))
    (hy4ne : y ≠ (block270S4 : ℝ)) :
    0 < block270V y := by
  have hcert := block270RightChunk000Certificate_eq_true
  unfold block270RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block270RightChunk000) (lo := block270RightChunk000L) (hi := block270RightChunk000R)
    (w1 := block270W1) (w2 := block270W2) (w3 := block270W3) (w4 := block270W4)
    (s1 := block270S1) (s2 := block270S2) (s3 := block270S3) (s4 := block270S4)
    hboxes hcover block270RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block270_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block270RightL : ℝ) (block270RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block270S1 : ℝ))
    (hy2ne : y ≠ (block270S2 : ℝ))
    (hy3ne : y ≠ (block270S3 : ℝ))
    (hy4ne : y ≠ (block270S4 : ℝ)) :
    0 < block270V y := by
  have hL : (block270RightChunk000L : ℝ) = (block270RightL : ℝ) := by
    norm_num [block270RightChunk000L, block270RightL]
  have hR : (block270RightChunk000R : ℝ) = (block270RightR : ℝ) := by
    norm_num [block270RightChunk000R, block270RightR]
  have hyc : y ∈ Icc (block270RightChunk000L : ℝ) (block270RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block270_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block270_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block270LeftL : ℝ) (block270LeftR : ℝ) →
    y ≠ 0 → y ≠ (block270S1 : ℝ) → y ≠ (block270S2 : ℝ) →
    y ≠ (block270S3 : ℝ) → y ≠ (block270S4 : ℝ) → 0 < block270V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block270RightL : ℝ) (block270RightR : ℝ) →
    y ≠ 0 → y ≠ (block270S1 : ℝ) → y ≠ (block270S2 : ℝ) →
    y ≠ (block270S3 : ℝ) → y ≠ (block270S4 : ℝ) → 0 < block270V y)

theorem block270_reallog_certificate_proof :
    block270_reallog_certificate := by
  exact ⟨block270_left_V_pos, block270_right_V_pos⟩

end Block270
end M1817475
end Erdos1038Lean
