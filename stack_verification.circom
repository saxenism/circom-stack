pragma circom 2.1.6;

include "node_modules/circomlib/circuits/comparators.circom";
include "node_modules/circomlib/circuits/multiplexer.circom";
include "node_modules/circomlib/circuits/gates.circom";

template IfElse() {
  signal input cond;
  signal input L;
  signal input R;
  signal output out;

  out <== cond * (L - R) + R;
}

template StackInsertion(max_depth) {
    signal input stack_state[max_depth];
    signal input current_pointer;
    signal input instruction;

    signal output out;

    var isPOP;

    component isEq = IsEqual();
    isEq.in[0] <== instruction;
    isEq.in[1] <== -1;

    isPOP = isEq.out;
    isPOP * (1 - isPOP) === 0;

    signal instruction_is_pop <== isPOP * current_pointer;
    signal instruction_is_push <== (1 - isPOP) * (current_pointer + 1);

    signal equality_pointer <==  instruction_is_pop + instruction_is_push;
    component isLessThan = LessThan(252);
    isLessThan.in[0] <== equality_pointer;
    isLessThan.in[1] <== max_depth;

    isLessThan.out === 1; // Constraining the equality_pointer to be less than the max_depth

    component multiplexer = Multiplexer(1, max_depth);
    var random_arr[max_depth][1];
    for(var i = 0; i < max_depth; i++) {
        random_arr[i][0] = stack_state[i];
    }

    component isZero = IsZero();

    multiplexer.inp <== random_arr;
    multiplexer.sel <== equality_pointer;

    isZero.in <== multiplexer.out[0] - instruction;
    out <== isZero.out;
}

template StackEquality(max_depth) {
    signal input stack_state_1[max_depth];
    signal input stack_state_2[max_depth];
    signal input current_pointer;
    signal input instruction;

    signal output out; // This *out signal* represents if the stack was equal upto the correct current_pointer
    signal output next_index;

    var isPOP;

    // The instruction that is in question, would be a POP instruction iff the instruction == field_size - 1
    component isEq = IsEqual();
    isEq.in[0] <== instruction;
    isEq.in[1] <== -1;

    isPOP = isEq.out;
    isPOP * (1 - isPOP) === 0;

    // If the POP instruction exists when the current_pointer is at 0, then that is an invalid state 
    // So, isPOP == 1 && current_pointer == -1 should be reverted.
    component isZero[2];

    isZero[0] = IsZero();
    isZero[1] = IsZero();
    
    isZero[0].in <== current_pointer + 1;
    isZero[1].in <== isPOP - 1;

    isZero[0].out * isZero[1].out === 0;

    signal inst_is_pop <== isPOP * (current_pointer - 1);
    signal inst_is_push <== (1 - isPOP) * current_pointer;
    signal check_index <== inst_is_pop + inst_is_push;

    signal comp_array[max_depth];
    component isEqual[max_depth];
    component isLET[max_depth];
    component ifElse[max_depth];
    
    for(var i = 0; i < max_depth; i++) {
        isEqual[i] = IsEqual();
        isLET[i] = LessEqThan(252);
        ifElse[i] = IfElse();

        isEqual[i].in[0] <== stack_state_1[i];
        isEqual[i].in[1] <== stack_state_2[i];

        isLET[i].in[0] <== i;
        isLET[i].in[1] <== check_index;

        // Since we only care about the equality of the stacks uptil the check_index
        // We will take the correct values upto check_index and post that make all values 1.
        ifElse[i].cond <== isLET[i].out;
        ifElse[i].L <== isEqual[i].out;
        ifElse[i].R <== 1;

        comp_array[i] <== ifElse[i].out;
    }

    component multiAND = MultiAND(max_depth);
    multiAND.in <== comp_array;

    signal instruction_is_pop <== isPOP * (current_pointer - 1);
    signal instruction_is_push <== (1 - isPOP) * (current_pointer + 1);

    next_index <== instruction_is_pop + instruction_is_push;

    // Doing a range check for next_index
    component isLE = LessThan(252);
    isLE.in[0] <== next_index;
    isLE.in[1] <== max_depth;

    isLE.out === 1;    
    out <== multiAND.out;
}

template StackOperation(max_depth) {
    signal input stack_state_1[max_depth];
    signal input stack_state_2[max_depth];
    signal input current_pointer;
    signal input instruction;
    
    signal output next_index; // We want this out signal to represent the next (correct) position of the current_index
    signal output out; // We want this *out signal* to represent if the given state transition was actually valid or not

    // Compare equality of stack_state_1 and stack_state_2 upto the curr_pointer
    // **THIS COMPONENT DOES NOT CHECK THE INVALID CASE OF CALLING POP ON EMPTY STACK**
    component stackEquality = StackEquality(max_depth);
    stackEquality.stack_state_1 <== stack_state_1;
    stackEquality.stack_state_2 <== stack_state_2;
    stackEquality.current_pointer <== current_pointer;
    stackEquality.instruction <== instruction;

    component stackInsertion = StackInsertion(max_depth);
    stackInsertion.stack_state <== stack_state_2;
    stackInsertion.current_pointer <== current_pointer;
    stackInsertion.instruction <== instruction;

    next_index <== stackEquality.next_index;
    // We want to make sure both the equality constraint and the correct insertion constraint hold
    // Ideally we would have done an AND of both values but since both values are binary, multiplying them would have the same result
    out <== stackEquality.out * stackInsertion.out; 
}

template StackVerification(n, max_depth, current_index) {
    /*
        We expect an input of different states of a stack 
        Those states should correspond to the stack instruction input
        This circuit needs to validate if the input states are indeed valid according to the instructions passed.
    */

    /*
        For simplicity's sake, we will use this format of instruction:
        1. If instructions[i] == some_number
            > That is equivalent to PUSH(some_number)
        2. If instructions[i] == -1 (field_size - 1)
            > That is equivalent to POP
    */

    // An input array of `n` stack instructions (PUSH and POP)
    signal input instructions[n];
    
    /*
        `n` instructions require `n+1` states of the stack for representation of those instructions
        1D represents the ith instance of the stack
        2D represents the state of the stack where index of the array is the index of the stack
    */
    // An input signal of arrays represeting different stack states
    /*
        In the stack_states, the stack would have some values pushed on to it.
        
        In our implementation, we will assume that whenever -1 is pushed onto the stack, it means that this is the index
        uptil where the stack had valid entries.

        And, we only expect the first stack_state to just have a single -1 entry to tell us
        exactly till which index is the stack filled.
    */
    signal input stack_states[n+1][max_depth];
    signal output out;
    
    // We create n+1 curr_index signals to track the current index for n+1 stacks
    signal curr_index[n+1]; 

    // We need to constraint that the current_index is not greater than or equal to the max_depth (since we count from 0)
    curr_index[0] <== current_index;
    component isLT = LessThan(252);
    isLT.in[0] <== curr_index[0];
    isLT.in[1] <== max_depth;

    isLT.out === 1;

    // Now we need to start checking if the transitions are correct or not
    // Our intention is to do and AND of all stOp output values and if it comes out to be 0, then the passed stack state transitions are invalid.                   
    signal multiANDArray[n];
    
    component stOp[n];
    for(var i = 0; i < n; i++) {
        stOp[i] = StackOperation(max_depth);

        stOp[i].stack_state_1 <== stack_states[i];
        stOp[i].stack_state_2 <== stack_states[i+1];
        stOp[i].current_pointer <== curr_index[i];
        stOp[i].instruction <== instructions[i];

        curr_index[i+1] <== stOp[i].next_index;

        multiANDArray[i] <== stOp[i].out;
    }

    component multiAND = MultiAND(n);
    multiAND.in <== multiANDArray;

    out <== multiAND.out;
}

component main { public [ instructions, stack_states ] } = StackVerification(3, 5, 2);

/* INPUT = {
    "instructions":[1, 12, -1],
    "stack_states":[[2,3,234, -1,-1],[2, 3,234, 1,-1],[2, 3, 234, 1, 12],[2, 3, 234, 1, -1]]
} */
