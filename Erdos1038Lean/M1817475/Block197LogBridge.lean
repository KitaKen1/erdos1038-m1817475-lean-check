import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block197

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block197

open Set

def block197W1 : Rat := ((304624613911379 : Rat) / 312500000000000)
def block197W2 : Rat := ((10080950508994417 : Rat) / 200000000000000000)
def block197W3 : Rat := ((8934482320843329 : Rat) / 50000000000000000)
def block197W4 : Rat := ((4784414797701423 : Rat) / 50000000000000000)
def block197S1 : Rat := ((18174751 : Rat) / 10000000)
def block197S2 : Rat := ((511587 : Rat) / 200000)
def block197S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block197S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block197V (y : ℝ) : ℝ :=
  ratPotential block197W1 block197W2 block197W3 block197W4 block197S1 block197S2 block197S3 block197S4 y

def block197LeftParamsCertificate : Bool :=
  allBoxesSameParams block197LeftBoxes block197W1 block197W2 block197W3 block197W4 block197S1 block197S2 block197S3 block197S4

theorem block197LeftParamsCertificate_eq_true :
    block197LeftParamsCertificate = true := by
  native_decide

theorem block197_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block197LeftL : ℝ) (block197LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block197S1 : ℝ))
    (hy2ne : y ≠ (block197S2 : ℝ))
    (hy3ne : y ≠ (block197S3 : ℝ))
    (hy4ne : y ≠ (block197S4 : ℝ)) :
    0 < block197V y := by
  have hcert := block197LeftCertificate_eq_true
  unfold block197LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block197LeftBoxes) (lo := block197LeftL) (hi := block197LeftR)
    (w1 := block197W1) (w2 := block197W2) (w3 := block197W3) (w4 := block197W4)
    (s1 := block197S1) (s2 := block197S2) (s3 := block197S3) (s4 := block197S4)
    hboxes hcover block197LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block197RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block197RightChunk000 block197W1 block197W2 block197W3 block197W4 block197S1 block197S2 block197S3 block197S4

theorem block197RightChunk000ParamsCertificate_eq_true :
    block197RightChunk000ParamsCertificate = true := by
  native_decide

theorem block197_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block197RightChunk000L : ℝ) (block197RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block197S1 : ℝ))
    (hy2ne : y ≠ (block197S2 : ℝ))
    (hy3ne : y ≠ (block197S3 : ℝ))
    (hy4ne : y ≠ (block197S4 : ℝ)) :
    0 < block197V y := by
  have hcert := block197RightChunk000Certificate_eq_true
  unfold block197RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block197RightChunk000) (lo := block197RightChunk000L) (hi := block197RightChunk000R)
    (w1 := block197W1) (w2 := block197W2) (w3 := block197W3) (w4 := block197W4)
    (s1 := block197S1) (s2 := block197S2) (s3 := block197S3) (s4 := block197S4)
    hboxes hcover block197RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block197RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block197RightChunk001 block197W1 block197W2 block197W3 block197W4 block197S1 block197S2 block197S3 block197S4

theorem block197RightChunk001ParamsCertificate_eq_true :
    block197RightChunk001ParamsCertificate = true := by
  native_decide

theorem block197_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block197RightChunk001L : ℝ) (block197RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block197S1 : ℝ))
    (hy2ne : y ≠ (block197S2 : ℝ))
    (hy3ne : y ≠ (block197S3 : ℝ))
    (hy4ne : y ≠ (block197S4 : ℝ)) :
    0 < block197V y := by
  have hcert := block197RightChunk001Certificate_eq_true
  unfold block197RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block197RightChunk001) (lo := block197RightChunk001L) (hi := block197RightChunk001R)
    (w1 := block197W1) (w2 := block197W2) (w3 := block197W3) (w4 := block197W4)
    (s1 := block197S1) (s2 := block197S2) (s3 := block197S3) (s4 := block197S4)
    hboxes hcover block197RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block197RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block197RightChunk002 block197W1 block197W2 block197W3 block197W4 block197S1 block197S2 block197S3 block197S4

theorem block197RightChunk002ParamsCertificate_eq_true :
    block197RightChunk002ParamsCertificate = true := by
  native_decide

theorem block197_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block197RightChunk002L : ℝ) (block197RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block197S1 : ℝ))
    (hy2ne : y ≠ (block197S2 : ℝ))
    (hy3ne : y ≠ (block197S3 : ℝ))
    (hy4ne : y ≠ (block197S4 : ℝ)) :
    0 < block197V y := by
  have hcert := block197RightChunk002Certificate_eq_true
  unfold block197RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block197RightChunk002) (lo := block197RightChunk002L) (hi := block197RightChunk002R)
    (w1 := block197W1) (w2 := block197W2) (w3 := block197W3) (w4 := block197W4)
    (s1 := block197S1) (s2 := block197S2) (s3 := block197S3) (s4 := block197S4)
    hboxes hcover block197RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block197RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block197RightChunk003 block197W1 block197W2 block197W3 block197W4 block197S1 block197S2 block197S3 block197S4

theorem block197RightChunk003ParamsCertificate_eq_true :
    block197RightChunk003ParamsCertificate = true := by
  native_decide

theorem block197_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block197RightChunk003L : ℝ) (block197RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block197S1 : ℝ))
    (hy2ne : y ≠ (block197S2 : ℝ))
    (hy3ne : y ≠ (block197S3 : ℝ))
    (hy4ne : y ≠ (block197S4 : ℝ)) :
    0 < block197V y := by
  have hcert := block197RightChunk003Certificate_eq_true
  unfold block197RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block197RightChunk003) (lo := block197RightChunk003L) (hi := block197RightChunk003R)
    (w1 := block197W1) (w2 := block197W2) (w3 := block197W3) (w4 := block197W4)
    (s1 := block197S1) (s2 := block197S2) (s3 := block197S3) (s4 := block197S4)
    hboxes hcover block197RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block197RightChunk004ParamsCertificate : Bool :=
  allBoxesSameParams block197RightChunk004 block197W1 block197W2 block197W3 block197W4 block197S1 block197S2 block197S3 block197S4

theorem block197RightChunk004ParamsCertificate_eq_true :
    block197RightChunk004ParamsCertificate = true := by
  native_decide

theorem block197_right_chunk004_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block197RightChunk004L : ℝ) (block197RightChunk004R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block197S1 : ℝ))
    (hy2ne : y ≠ (block197S2 : ℝ))
    (hy3ne : y ≠ (block197S3 : ℝ))
    (hy4ne : y ≠ (block197S4 : ℝ)) :
    0 < block197V y := by
  have hcert := block197RightChunk004Certificate_eq_true
  unfold block197RightChunk004Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block197RightChunk004) (lo := block197RightChunk004L) (hi := block197RightChunk004R)
    (w1 := block197W1) (w2 := block197W2) (w3 := block197W3) (w4 := block197W4)
    (s1 := block197S1) (s2 := block197S2) (s3 := block197S3) (s4 := block197S4)
    hboxes hcover block197RightChunk004ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block197RightChunk005ParamsCertificate : Bool :=
  allBoxesSameParams block197RightChunk005 block197W1 block197W2 block197W3 block197W4 block197S1 block197S2 block197S3 block197S4

theorem block197RightChunk005ParamsCertificate_eq_true :
    block197RightChunk005ParamsCertificate = true := by
  native_decide

theorem block197_right_chunk005_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block197RightChunk005L : ℝ) (block197RightChunk005R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block197S1 : ℝ))
    (hy2ne : y ≠ (block197S2 : ℝ))
    (hy3ne : y ≠ (block197S3 : ℝ))
    (hy4ne : y ≠ (block197S4 : ℝ)) :
    0 < block197V y := by
  have hcert := block197RightChunk005Certificate_eq_true
  unfold block197RightChunk005Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block197RightChunk005) (lo := block197RightChunk005L) (hi := block197RightChunk005R)
    (w1 := block197W1) (w2 := block197W2) (w3 := block197W3) (w4 := block197W4)
    (s1 := block197S1) (s2 := block197S2) (s3 := block197S3) (s4 := block197S4)
    hboxes hcover block197RightChunk005ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block197RightChunk006ParamsCertificate : Bool :=
  allBoxesSameParams block197RightChunk006 block197W1 block197W2 block197W3 block197W4 block197S1 block197S2 block197S3 block197S4

theorem block197RightChunk006ParamsCertificate_eq_true :
    block197RightChunk006ParamsCertificate = true := by
  native_decide

theorem block197_right_chunk006_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block197RightChunk006L : ℝ) (block197RightChunk006R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block197S1 : ℝ))
    (hy2ne : y ≠ (block197S2 : ℝ))
    (hy3ne : y ≠ (block197S3 : ℝ))
    (hy4ne : y ≠ (block197S4 : ℝ)) :
    0 < block197V y := by
  have hcert := block197RightChunk006Certificate_eq_true
  unfold block197RightChunk006Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block197RightChunk006) (lo := block197RightChunk006L) (hi := block197RightChunk006R)
    (w1 := block197W1) (w2 := block197W2) (w3 := block197W3) (w4 := block197W4)
    (s1 := block197S1) (s2 := block197S2) (s3 := block197S3) (s4 := block197S4)
    hboxes hcover block197RightChunk006ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block197RightChunk007ParamsCertificate : Bool :=
  allBoxesSameParams block197RightChunk007 block197W1 block197W2 block197W3 block197W4 block197S1 block197S2 block197S3 block197S4

theorem block197RightChunk007ParamsCertificate_eq_true :
    block197RightChunk007ParamsCertificate = true := by
  native_decide

theorem block197_right_chunk007_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block197RightChunk007L : ℝ) (block197RightChunk007R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block197S1 : ℝ))
    (hy2ne : y ≠ (block197S2 : ℝ))
    (hy3ne : y ≠ (block197S3 : ℝ))
    (hy4ne : y ≠ (block197S4 : ℝ)) :
    0 < block197V y := by
  have hcert := block197RightChunk007Certificate_eq_true
  unfold block197RightChunk007Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block197RightChunk007) (lo := block197RightChunk007L) (hi := block197RightChunk007R)
    (w1 := block197W1) (w2 := block197W2) (w3 := block197W3) (w4 := block197W4)
    (s1 := block197S1) (s2 := block197S2) (s3 := block197S3) (s4 := block197S4)
    hboxes hcover block197RightChunk007ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block197RightChunk008ParamsCertificate : Bool :=
  allBoxesSameParams block197RightChunk008 block197W1 block197W2 block197W3 block197W4 block197S1 block197S2 block197S3 block197S4

theorem block197RightChunk008ParamsCertificate_eq_true :
    block197RightChunk008ParamsCertificate = true := by
  native_decide

theorem block197_right_chunk008_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block197RightChunk008L : ℝ) (block197RightChunk008R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block197S1 : ℝ))
    (hy2ne : y ≠ (block197S2 : ℝ))
    (hy3ne : y ≠ (block197S3 : ℝ))
    (hy4ne : y ≠ (block197S4 : ℝ)) :
    0 < block197V y := by
  have hcert := block197RightChunk008Certificate_eq_true
  unfold block197RightChunk008Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block197RightChunk008) (lo := block197RightChunk008L) (hi := block197RightChunk008R)
    (w1 := block197W1) (w2 := block197W2) (w3 := block197W3) (w4 := block197W4)
    (s1 := block197S1) (s2 := block197S2) (s3 := block197S3) (s4 := block197S4)
    hboxes hcover block197RightChunk008ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block197RightChunk009ParamsCertificate : Bool :=
  allBoxesSameParams block197RightChunk009 block197W1 block197W2 block197W3 block197W4 block197S1 block197S2 block197S3 block197S4

theorem block197RightChunk009ParamsCertificate_eq_true :
    block197RightChunk009ParamsCertificate = true := by
  native_decide

theorem block197_right_chunk009_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block197RightChunk009L : ℝ) (block197RightChunk009R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block197S1 : ℝ))
    (hy2ne : y ≠ (block197S2 : ℝ))
    (hy3ne : y ≠ (block197S3 : ℝ))
    (hy4ne : y ≠ (block197S4 : ℝ)) :
    0 < block197V y := by
  have hcert := block197RightChunk009Certificate_eq_true
  unfold block197RightChunk009Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block197RightChunk009) (lo := block197RightChunk009L) (hi := block197RightChunk009R)
    (w1 := block197W1) (w2 := block197W2) (w3 := block197W3) (w4 := block197W4)
    (s1 := block197S1) (s2 := block197S2) (s3 := block197S3) (s4 := block197S4)
    hboxes hcover block197RightChunk009ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block197RightChunk010ParamsCertificate : Bool :=
  allBoxesSameParams block197RightChunk010 block197W1 block197W2 block197W3 block197W4 block197S1 block197S2 block197S3 block197S4

theorem block197RightChunk010ParamsCertificate_eq_true :
    block197RightChunk010ParamsCertificate = true := by
  native_decide

theorem block197_right_chunk010_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block197RightChunk010L : ℝ) (block197RightChunk010R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block197S1 : ℝ))
    (hy2ne : y ≠ (block197S2 : ℝ))
    (hy3ne : y ≠ (block197S3 : ℝ))
    (hy4ne : y ≠ (block197S4 : ℝ)) :
    0 < block197V y := by
  have hcert := block197RightChunk010Certificate_eq_true
  unfold block197RightChunk010Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block197RightChunk010) (lo := block197RightChunk010L) (hi := block197RightChunk010R)
    (w1 := block197W1) (w2 := block197W2) (w3 := block197W3) (w4 := block197W4)
    (s1 := block197S1) (s2 := block197S2) (s3 := block197S3) (s4 := block197S4)
    hboxes hcover block197RightChunk010ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block197RightChunk011ParamsCertificate : Bool :=
  allBoxesSameParams block197RightChunk011 block197W1 block197W2 block197W3 block197W4 block197S1 block197S2 block197S3 block197S4

theorem block197RightChunk011ParamsCertificate_eq_true :
    block197RightChunk011ParamsCertificate = true := by
  native_decide

theorem block197_right_chunk011_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block197RightChunk011L : ℝ) (block197RightChunk011R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block197S1 : ℝ))
    (hy2ne : y ≠ (block197S2 : ℝ))
    (hy3ne : y ≠ (block197S3 : ℝ))
    (hy4ne : y ≠ (block197S4 : ℝ)) :
    0 < block197V y := by
  have hcert := block197RightChunk011Certificate_eq_true
  unfold block197RightChunk011Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block197RightChunk011) (lo := block197RightChunk011L) (hi := block197RightChunk011R)
    (w1 := block197W1) (w2 := block197W2) (w3 := block197W3) (w4 := block197W4)
    (s1 := block197S1) (s2 := block197S2) (s3 := block197S3) (s4 := block197S4)
    hboxes hcover block197RightChunk011ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block197RightChunk012ParamsCertificate : Bool :=
  allBoxesSameParams block197RightChunk012 block197W1 block197W2 block197W3 block197W4 block197S1 block197S2 block197S3 block197S4

theorem block197RightChunk012ParamsCertificate_eq_true :
    block197RightChunk012ParamsCertificate = true := by
  native_decide

theorem block197_right_chunk012_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block197RightChunk012L : ℝ) (block197RightChunk012R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block197S1 : ℝ))
    (hy2ne : y ≠ (block197S2 : ℝ))
    (hy3ne : y ≠ (block197S3 : ℝ))
    (hy4ne : y ≠ (block197S4 : ℝ)) :
    0 < block197V y := by
  have hcert := block197RightChunk012Certificate_eq_true
  unfold block197RightChunk012Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block197RightChunk012) (lo := block197RightChunk012L) (hi := block197RightChunk012R)
    (w1 := block197W1) (w2 := block197W2) (w3 := block197W3) (w4 := block197W4)
    (s1 := block197S1) (s2 := block197S2) (s3 := block197S3) (s4 := block197S4)
    hboxes hcover block197RightChunk012ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block197_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block197RightL : ℝ) (block197RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block197S1 : ℝ))
    (hy2ne : y ≠ (block197S2 : ℝ))
    (hy3ne : y ≠ (block197S3 : ℝ))
    (hy4ne : y ≠ (block197S4 : ℝ)) :
    0 < block197V y := by
  by_cases h0 : y ≤ (block197RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block197RightChunk000L : ℝ) (block197RightChunk000R : ℝ) := by
      have hL : (block197RightChunk000L : ℝ) = (block197RightL : ℝ) := by
        norm_num [block197RightChunk000L, block197RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block197_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block197RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block197RightChunk001L : ℝ) (block197RightChunk001R : ℝ) := by
        have hprev : (block197RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block197RightChunk001L : ℝ) = (block197RightChunk000R : ℝ) := by
          norm_num [block197RightChunk001L, block197RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block197_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block197RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block197RightChunk002L : ℝ) (block197RightChunk002R : ℝ) := by
          have hprev : (block197RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block197RightChunk002L : ℝ) = (block197RightChunk001R : ℝ) := by
            norm_num [block197RightChunk002L, block197RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block197_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        by_cases h3 : y ≤ (block197RightChunk003R : ℝ)
        · have hyc : y ∈ Icc (block197RightChunk003L : ℝ) (block197RightChunk003R : ℝ) := by
            have hprev : (block197RightChunk002R : ℝ) < y := lt_of_not_ge h2
            have hL : (block197RightChunk003L : ℝ) = (block197RightChunk002R : ℝ) := by
              norm_num [block197RightChunk003L, block197RightChunk002R]
            constructor
            · linarith [hprev, hL]
            · exact h3
          exact block197_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
        ·
          by_cases h4 : y ≤ (block197RightChunk004R : ℝ)
          · have hyc : y ∈ Icc (block197RightChunk004L : ℝ) (block197RightChunk004R : ℝ) := by
              have hprev : (block197RightChunk003R : ℝ) < y := lt_of_not_ge h3
              have hL : (block197RightChunk004L : ℝ) = (block197RightChunk003R : ℝ) := by
                norm_num [block197RightChunk004L, block197RightChunk003R]
              constructor
              · linarith [hprev, hL]
              · exact h4
            exact block197_right_chunk004_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
          ·
            by_cases h5 : y ≤ (block197RightChunk005R : ℝ)
            · have hyc : y ∈ Icc (block197RightChunk005L : ℝ) (block197RightChunk005R : ℝ) := by
                have hprev : (block197RightChunk004R : ℝ) < y := lt_of_not_ge h4
                have hL : (block197RightChunk005L : ℝ) = (block197RightChunk004R : ℝ) := by
                  norm_num [block197RightChunk005L, block197RightChunk004R]
                constructor
                · linarith [hprev, hL]
                · exact h5
              exact block197_right_chunk005_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
            ·
              by_cases h6 : y ≤ (block197RightChunk006R : ℝ)
              · have hyc : y ∈ Icc (block197RightChunk006L : ℝ) (block197RightChunk006R : ℝ) := by
                  have hprev : (block197RightChunk005R : ℝ) < y := lt_of_not_ge h5
                  have hL : (block197RightChunk006L : ℝ) = (block197RightChunk005R : ℝ) := by
                    norm_num [block197RightChunk006L, block197RightChunk005R]
                  constructor
                  · linarith [hprev, hL]
                  · exact h6
                exact block197_right_chunk006_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
              ·
                by_cases h7 : y ≤ (block197RightChunk007R : ℝ)
                · have hyc : y ∈ Icc (block197RightChunk007L : ℝ) (block197RightChunk007R : ℝ) := by
                    have hprev : (block197RightChunk006R : ℝ) < y := lt_of_not_ge h6
                    have hL : (block197RightChunk007L : ℝ) = (block197RightChunk006R : ℝ) := by
                      norm_num [block197RightChunk007L, block197RightChunk006R]
                    constructor
                    · linarith [hprev, hL]
                    · exact h7
                  exact block197_right_chunk007_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
                ·
                  by_cases h8 : y ≤ (block197RightChunk008R : ℝ)
                  · have hyc : y ∈ Icc (block197RightChunk008L : ℝ) (block197RightChunk008R : ℝ) := by
                      have hprev : (block197RightChunk007R : ℝ) < y := lt_of_not_ge h7
                      have hL : (block197RightChunk008L : ℝ) = (block197RightChunk007R : ℝ) := by
                        norm_num [block197RightChunk008L, block197RightChunk007R]
                      constructor
                      · linarith [hprev, hL]
                      · exact h8
                    exact block197_right_chunk008_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
                  ·
                    by_cases h9 : y ≤ (block197RightChunk009R : ℝ)
                    · have hyc : y ∈ Icc (block197RightChunk009L : ℝ) (block197RightChunk009R : ℝ) := by
                        have hprev : (block197RightChunk008R : ℝ) < y := lt_of_not_ge h8
                        have hL : (block197RightChunk009L : ℝ) = (block197RightChunk008R : ℝ) := by
                          norm_num [block197RightChunk009L, block197RightChunk008R]
                        constructor
                        · linarith [hprev, hL]
                        · exact h9
                      exact block197_right_chunk009_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
                    ·
                      by_cases h10 : y ≤ (block197RightChunk010R : ℝ)
                      · have hyc : y ∈ Icc (block197RightChunk010L : ℝ) (block197RightChunk010R : ℝ) := by
                          have hprev : (block197RightChunk009R : ℝ) < y := lt_of_not_ge h9
                          have hL : (block197RightChunk010L : ℝ) = (block197RightChunk009R : ℝ) := by
                            norm_num [block197RightChunk010L, block197RightChunk009R]
                          constructor
                          · linarith [hprev, hL]
                          · exact h10
                        exact block197_right_chunk010_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
                      ·
                        by_cases h11 : y ≤ (block197RightChunk011R : ℝ)
                        · have hyc : y ∈ Icc (block197RightChunk011L : ℝ) (block197RightChunk011R : ℝ) := by
                            have hprev : (block197RightChunk010R : ℝ) < y := lt_of_not_ge h10
                            have hL : (block197RightChunk011L : ℝ) = (block197RightChunk010R : ℝ) := by
                              norm_num [block197RightChunk011L, block197RightChunk010R]
                            constructor
                            · linarith [hprev, hL]
                            · exact h11
                          exact block197_right_chunk011_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
                        ·
                          have hprev : (block197RightChunk011R : ℝ) < y := lt_of_not_ge h11
                          have hL : (block197RightChunk012L : ℝ) = (block197RightChunk011R : ℝ) := by
                            norm_num [block197RightChunk012L, block197RightChunk011R]
                          have hR : (block197RightChunk012R : ℝ) = (block197RightR : ℝ) := by
                            norm_num [block197RightChunk012R, block197RightR]
                          have hyc : y ∈ Icc (block197RightChunk012L : ℝ) (block197RightChunk012R : ℝ) := by
                            constructor
                            · linarith [hprev, hL]
                            · linarith [hy.2, hR]
                          exact block197_right_chunk012_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block197_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block197LeftL : ℝ) (block197LeftR : ℝ) →
    y ≠ 0 → y ≠ (block197S1 : ℝ) → y ≠ (block197S2 : ℝ) →
    y ≠ (block197S3 : ℝ) → y ≠ (block197S4 : ℝ) → 0 < block197V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block197RightL : ℝ) (block197RightR : ℝ) →
    y ≠ 0 → y ≠ (block197S1 : ℝ) → y ≠ (block197S2 : ℝ) →
    y ≠ (block197S3 : ℝ) → y ≠ (block197S4 : ℝ) → 0 < block197V y)

theorem block197_reallog_certificate_proof :
    block197_reallog_certificate := by
  exact ⟨block197_left_V_pos, block197_right_V_pos⟩

end Block197
end M1817475
end Erdos1038Lean
