import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block450

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block450

open Set

def block450W1 : Rat := ((5976684002064457 : Rat) / 10000000000000000)
def block450W2 : Rat := (0 : Rat)
def block450W3 : Rat := ((33283679697666113 : Rat) / 100000000000000000)
def block450W4 : Rat := ((1682309473947059 : Rat) / 25000000000000000)
def block450S1 : Rat := ((18174751 : Rat) / 10000000)
def block450S2 : Rat := ((511587 : Rat) / 200000)
def block450S3 : Rat := ((131336459017857142963 : Rat) / 50000000000000000000)
def block450S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block450V (y : ℝ) : ℝ :=
  ratPotential block450W1 block450W2 block450W3 block450W4 block450S1 block450S2 block450S3 block450S4 y

def block450LeftParamsCertificate : Bool :=
  allBoxesSameParams block450LeftBoxes block450W1 block450W2 block450W3 block450W4 block450S1 block450S2 block450S3 block450S4

theorem block450LeftParamsCertificate_eq_true :
    block450LeftParamsCertificate = true := by
  native_decide

theorem block450_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block450LeftL : ℝ) (block450LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block450S1 : ℝ))
    (hy2ne : y ≠ (block450S2 : ℝ))
    (hy3ne : y ≠ (block450S3 : ℝ))
    (hy4ne : y ≠ (block450S4 : ℝ)) :
    0 < block450V y := by
  have hcert := block450LeftCertificate_eq_true
  unfold block450LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block450LeftBoxes) (lo := block450LeftL) (hi := block450LeftR)
    (w1 := block450W1) (w2 := block450W2) (w3 := block450W3) (w4 := block450W4)
    (s1 := block450S1) (s2 := block450S2) (s3 := block450S3) (s4 := block450S4)
    hboxes hcover block450LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block450RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block450RightChunk000 block450W1 block450W2 block450W3 block450W4 block450S1 block450S2 block450S3 block450S4

theorem block450RightChunk000ParamsCertificate_eq_true :
    block450RightChunk000ParamsCertificate = true := by
  native_decide

theorem block450_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block450RightChunk000L : ℝ) (block450RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block450S1 : ℝ))
    (hy2ne : y ≠ (block450S2 : ℝ))
    (hy3ne : y ≠ (block450S3 : ℝ))
    (hy4ne : y ≠ (block450S4 : ℝ)) :
    0 < block450V y := by
  have hcert := block450RightChunk000Certificate_eq_true
  unfold block450RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block450RightChunk000) (lo := block450RightChunk000L) (hi := block450RightChunk000R)
    (w1 := block450W1) (w2 := block450W2) (w3 := block450W3) (w4 := block450W4)
    (s1 := block450S1) (s2 := block450S2) (s3 := block450S3) (s4 := block450S4)
    hboxes hcover block450RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block450_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block450RightL : ℝ) (block450RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block450S1 : ℝ))
    (hy2ne : y ≠ (block450S2 : ℝ))
    (hy3ne : y ≠ (block450S3 : ℝ))
    (hy4ne : y ≠ (block450S4 : ℝ)) :
    0 < block450V y := by
  have hL : (block450RightChunk000L : ℝ) = (block450RightL : ℝ) := by
    norm_num [block450RightChunk000L, block450RightL]
  have hR : (block450RightChunk000R : ℝ) = (block450RightR : ℝ) := by
    norm_num [block450RightChunk000R, block450RightR]
  have hyc : y ∈ Icc (block450RightChunk000L : ℝ) (block450RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block450_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block450_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block450LeftL : ℝ) (block450LeftR : ℝ) →
    y ≠ 0 → y ≠ (block450S1 : ℝ) → y ≠ (block450S2 : ℝ) →
    y ≠ (block450S3 : ℝ) → y ≠ (block450S4 : ℝ) → 0 < block450V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block450RightL : ℝ) (block450RightR : ℝ) →
    y ≠ 0 → y ≠ (block450S1 : ℝ) → y ≠ (block450S2 : ℝ) →
    y ≠ (block450S3 : ℝ) → y ≠ (block450S4 : ℝ) → 0 < block450V y)

theorem block450_reallog_certificate_proof :
    block450_reallog_certificate := by
  exact ⟨block450_left_V_pos, block450_right_V_pos⟩

end Block450
end M1817475
end Erdos1038Lean
