// Source for the test AuRa validator set contract.
//
// The bytecode of this contract is included in `validator_contract.json` as the
// constructor of address `0x0000..0005`.

pragma solidity ^0.5.0;

contract TestList {
	address[] public validators = [
		0x7d577a597B2742b498Cb5Cf0C26cDCD726d39E6e,
		0x82A978B3f5962A5b0957d9ee9eEf472EE55B42F1
	];
	address[] public pendingValidators = [
		0x7d577a597B2742b498Cb5Cf0C26cDCD726d39E6e,
		0x82A978B3f5962A5b0957d9ee9eEf472EE55B42F1
	];
	mapping(address => uint) indices;

	event InitiateChange(bytes32 indexed parentHash, address[] newSet);

	constructor() public {
		for (uint i = 0; i < validators.length; i++) {
			indices[validators[i]] = i;
		}
	}

	// Returns the current validators.
	function getValidators() view public returns (address[] memory) {
		return validators;
	}

	// Removes a validator from the list.
	function reportMalicious(address validator, uint256 _blockNumber, bytes memory _proof) public {
		pendingValidators[indices[validator]] = pendingValidators[pendingValidators.length-1];
		delete indices[validator];
		delete pendingValidators[pendingValidators.length-1];
		pendingValidators.length--;
		// Log the validator set change.
		emit InitiateChange(blockhash(block.number - 1), pendingValidators);
	}

	// Checks if `emitInitiateChange` can be called.
	function emitInitiateChangeCallable() pure public returns (bool) {
		return true;
	}

	// Emits an `InitiateChange` event in production code. Does nothing in the test.
	function emitInitiateChange() external {}

	// Applies a validator set change.
	function finalizeChange() public {
	    uint i;
	    uint len = validators.length;
	    for (i = 0; i < len; i++) {
	        delete validators[i];
	    }
	    validators.length = 0;
	    for (i = 0; i < pendingValidators.length; i++) {
	        validators.push(pendingValidators[i]);
	    }
	}
}
