const fungibleTokenContract = `
scilla_version 0

(***************************************************)
(*               Associated library                *)
(***************************************************)
import IntUtils
library FungibleToken

let one_msg = 
  fun (msg : Message) => 
  let nil_msg = Nil {Message} in
  Cons {Message} msg nil_msg

let two_msgs =
fun (msg1 : Message) =>
fun (msg2 : Message) =>
  let msgs_tmp = one_msg msg2 in
  Cons {Message} msg1 msgs_tmp

(* Error events *)
type Error =
| CodeIsSender
| CodeInsufficientFunds
| CodeInsufficientAllowance

let make_error =
  fun (result : Error) =>
    let result_code = 
      match result with
      | CodeIsSender              => Int32 -1
      | CodeInsufficientFunds     => Int32 -2
      | CodeInsufficientAllowance => Int32 -3
      end
    in
    { _exception : "Error"; code : result_code }
  
let zero = Uint128 0

(* Dummy user-defined ADT *)
type Unit =
| Unit

let get_val =
  fun (some_val: Option Uint128) =>
  match some_val with
  | Some val => val
  | None => zero
  end

(***************************************************)
(*             The contract definition             *)
(***************************************************)

contract FungibleToken
(
  contract_owner: ByStr20,
  name : String,
  symbol: String,
  decimals: Uint32,
  init_supply : Uint128
)

(* Mutable fields *)

field total_supply : Uint128 = init_supply

field balances: Map ByStr20 Uint128 
  = let emp_map = Emp ByStr20 Uint128 in
    builtin put emp_map contract_owner init_supply

field allowances: Map ByStr20 (Map ByStr20 Uint128) 
  = Emp ByStr20 (Map ByStr20 Uint128)

(**************************************)
(*             Procedures             *)
(**************************************)

procedure ThrowError(err : Error)
  e = make_error err;
  throw e
end

procedure IsNotSender(address: ByStr20)
  is_sender = builtin eq _sender address;
  match is_sender with
  | True =>
    err = CodeIsSender;
    ThrowError err
  | False =>
  end
end

procedure AuthorizedMoveIfSufficientBalance(from: ByStr20, to: ByStr20, amount: Uint128)
  o_from_bal <- balances[from];
  bal = get_val o_from_bal;
  can_do = uint128_le amount bal;
  match can_do with
  | True =>
    (* Subtract amount from from and add it to to address *)
    new_from_bal = builtin sub bal amount;
    balances[from] := new_from_bal;
    (* Adds amount to to address *)
    get_to_bal <- balances[to];
    new_to_bal = match get_to_bal with
    | Some bal => builtin add bal amount
    | None => amount
    end;
    balances[to] := new_to_bal
  | False =>
    (* Balance not sufficient *)
    err = CodeInsufficientFunds;
    ThrowError err
  end
end

(***************************************)
(*             Transitions             *)
(***************************************)

(* @dev: Increase the allowance of an approved_spender over the caller tokens. Only token_owner allowed to invoke.   *)
(* param spender:      Address of the designated approved_spender.                                                   *)
(* param amount:       Number of tokens to be increased as allowance for the approved_spender.                       *)
transition IncreaseAllowance(spender: ByStr20, amount: Uint128)
  IsNotSender spender;
  some_current_allowance <- allowances[_sender][spender];
  current_allowance = get_val some_current_allowance;
  new_allowance = builtin add current_allowance amount;
  allowances[_sender][spender] := new_allowance;
  e = {_eventname : "IncreasedAllowance"; token_owner : _sender; spender: spender; new_allowance : new_allowance};
  event e
end

(* @dev: Decrease the allowance of an approved_spender over the caller tokens. Only token_owner allowed to invoke. *)
(* param spender:      Address of the designated approved_spender.                                                 *)
(* param amount:       Number of tokens to be decreased as allowance for the approved_spender.                     *)
transition DecreaseAllowance(spender: ByStr20, amount: Uint128)
  IsNotSender spender;
  some_current_allowance <- allowances[_sender][spender];
  current_allowance = get_val some_current_allowance;
  new_allowance =
    let amount_le_allowance = uint128_le amount current_allowance in
      match amount_le_allowance with
      | True => builtin sub current_allowance amount
      | False => zero
      end;
  allowances[_sender][spender] := new_allowance;
  e = {_eventname : "DecreasedAllowance"; token_owner : _sender; spender: spender; new_allowance : new_allowance};
  event e
end

(* @dev: Moves an amount tokens from _sender to the recipient. Used by token_owner. *)
(* @dev: Balance of recipient will increase. Balance of _sender will decrease.      *)
(* @param to:  Address of the recipient whose balance is increased.                 *)
(* @param amount:     Amount of tokens to be sent.                                  *)
transition Transfer(to: ByStr20, amount: Uint128)
  AuthorizedMoveIfSufficientBalance _sender to amount;
  e = {_eventname : "TransferSuccess"; sender : _sender; recipient : to; amount : amount};
  event e;
  (* Prevent sending to a contract address that does not support transfers of token *)
  msg_to_recipient = {_tag : "RecipientAcceptTransfer"; _recipient : to; _amount : zero; 
                      sender : _sender; recipient : to; amount : amount};
  msg_to_sender = {_tag : "TransferSuccessCallBack"; _recipient : _sender; _amount : zero; 
                  sender : _sender; recipient : to; amount : amount};
  msgs = two_msgs msg_to_recipient msg_to_sender;
  send msgs
end

(* @dev: Move a given amount of tokens from one address to another using the allowance mechanism. The caller must be an approved_spender. *)
(* @dev: Balance of recipient will increase. Balance of token_owner will decrease.                                                        *)
(* @param from:    Address of the token_owner whose balance is decreased.                                                                 *)
(* @param to:      Address of the recipient whose balance is increased.                                                                   *)
(* @param amount:  Amount of tokens to be transferred.                                                                                    *)
transition TransferFrom(from: ByStr20, to: ByStr20, amount: Uint128)
  o_spender_allowed <- allowances[from][_sender];
  allowed = get_val o_spender_allowed;
  can_do = uint128_le amount allowed;
  match can_do with
  | True =>
    AuthorizedMoveIfSufficientBalance from to amount;
    e = {_eventname : "TransferFromSuccess"; initiator : _sender; sender : from; recipient : to; amount : amount};
    event e;
    new_allowed = builtin sub allowed amount;
    allowances[from][_sender] := new_allowed;
    (* Prevent sending to a contract address that does not support transfers of token *)
    msg_to_recipient = {_tag: "RecipientAcceptTransferFrom"; _recipient : to; _amount: zero; 
                        initiator: _sender; sender : from; recipient: to; amount: amount};
    msg_to_sender = {_tag: "TransferFromSuccessCallBack"; _recipient: _sender; _amount: zero; 
                    initiator: _sender; sender: from; recipient: to; amount: amount};
    msgs = two_msgs msg_to_recipient msg_to_sender;
    send msgs
  | False =>
    err = CodeInsufficientAllowance;
    ThrowError err
  end
end
`

//wait for DOM to load and parse
window.addEventListener('DOMContentLoaded', (event) => {
    const connectButton = document.getElementById("connect");
    const deployButton = document.getElementById("deployContract");

    let zilliqa = null;
    let crypto = null;

    //check for connect button click
    connectButton.addEventListener('click', function() {
        if (typeof window.zilPay !== 'undefined') {
            return zilPay.wallet.connect().then(function(accounts) {
                zilliqa = window.zilPay;
                crypto = zilPay.crypto;

                $('#connect').fadeOut(600);
                $('#tokenForm').delay(500).fadeIn(600);
                $('#blob').width('200%');
            })
        } else {
            alert("Couldn't find zilPay");
        }
    });

    deployButton.addEventListener('click', function() {
        const input_owner = document.getElementById("input_owner").value;
        const input_name = document.getElementById("input_name").value;
        const input_symbol = document.getElementById("input_ticker").value;
        const input_decimal = document.getElementById("input_decimal").value;
        const input_supply = document.getElementById("input_supply").value;

        deployContract(input_owner, input_name, input_symbol, input_decimal, input_supply);
    });
});

function deployContract(owner, name, symbol, decimal, supply) {
    let supplyDecimals = "";

    for (let i = 0; i < decimal; i++) {
        supplyDecimals += "0";
    }

    supplyDecimals = supply.toString() + supplyDecimals;

    const init = [{
            "vname": "contract_owner",
            "type": "ByStr20",
            "value": window.zilPay.crypto.fromBech32Address(owner)
        },
        {
            "vname": "name",
            "type": "String",
            "value": name
        },
        {
            "vname": "symbol",
            "type": "String",
            "value": symbol
        },
        {
            "vname": "decimals",
            "type": "Uint32",
            "value": decimal
        },
        {
            "vname": "init_supply",
            "type": "Uint128",
            "value": supplyDecimals
        },
        {
            "vname": "_scilla_version",
            "type": "Uint32",
            "value": "0"
        }
    ]

    // Create contract instance with some methods
    const contract = zilPay
        .contracts
        .new(fungibleTokenContract, init);

    // Sending to TX
    contract.deploy({
            gasLimit: '25000',
            gasPrice: '1000000000'
        })
        .then(([tx, contract]) => window.open("https://viewblock.io/zilliqa/tx/" + tx.TranID));
}