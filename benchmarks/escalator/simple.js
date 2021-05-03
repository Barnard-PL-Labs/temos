// This module is intended to be used with the TSL Synthesis Synthesizer.
// Visit the project repository: https://github.com/Barnard-PL-Labs/TSLSynthesizer

function control({ s_bottom
, s_top
, s_up
}){

    // Cells
    let c_up = s_up;

    // Terms
    let w3 = f_False();
    let w4 = f_True();
    let b5 = p_gt(s_bottom, s_top);

    let innerCircuit = controlCircuit(b5);

    // Switches
    let o_up = upSwitch([w3, innerCircuit[0]], [w4, innerCircuit[1]], [c_up, innerCircuit[2]]);


    return [o_up];
}

/////////////////////////////////////////////////////////////////////////////

function upSwitch
    ( p0
    , p1
    , p2
    ){
    const r1 = p1[1] ? p1[0] : p2[0]; 
    const r0 = p0[1] ? p0[0] : r1;
    return r0;
}





function controlCircuit
    (cin0){

    // Latches
    // Gates

    // Outputs
    const o0 = !cin0;

    return [ o0
           , cin0
           , false];

 }

/////////////////////////////////////////////////////////////////////////////

// Implemented Functions
function p_play(input){return input;}
function p_press(input){return input;}
function p_change(input){return input;}
function p_veloBelow50(velocity){return velocity<=50}
function p_veloAbove50(velocity){return velocity>50}
function f_True(){return true;}
function f_False(){return false;}
function f_sawtooth(){return "sawtooth";}
function f_sine(){return "sine";}
function f_square(){return "square";}
function f_triangle(){return "triangle";}
function f_upStyle(){return "up";}
function f_downStyle(){return "down";}
function f_upDownStyle(){return "up-down";}
function f_randomStyle(){return "random";}
function f_lowpass(){return "lowpass";}
function f_highpass(){return "highpass";}
function f_bandpass(){return "bandpass";}
function f_toggle(input){return !input};
function f_inc1000(arg){return arg+1000;}
function f_dec1000(arg){return Math.max(arg-1000,0);}
function f_inc100(arg){return Math.min(arg+100,10000);}
function f_dec100(arg){return Math.max(arg-100,20);}
function f_inc10(arg){return arg+10;}
function f_dec10(arg){return Math.max(arg-10,0);}
function f_inc1(arg){return arg+1;}
function f_dec1(arg){return Math.max(arg-1,0);}
function f_inc1max12(arg){return Math.min(arg+1,12);}
function f_dec1min12(arg){return Math.max(arg-1,-12);}
function f_getWaveformVal(node){return waveformControl.value}
function f_getArpType(node){return arpeggiatorStyleControl.value}


// Notes
var bottom = document.getElementById("bottom");
var top = document.getElementById("top");
var up = document.getElementById("up");

// Reactive Updates
[up] = control({
    s_bottom : false,
    s_top : false,
    s_up : false,
    s_keyboardNode : false});
updateVarsToUI();

bottom.addEventListener("click", _ => {
    [up] = control({
        s_bottom : true,
        s_top : false,
        s_up : false,
        s_keyboardNode : false});
    updateVarsToUI();
});

top.addEventListener("click", _ => {
    [up] = control({
        s_bottom : false,
        s_top : true,
        s_up : false,
        s_keyboardNode : false});
    updateVarsToUI();
});

up.addEventListener("click", _ => {
    [up] = control({
        s_bottom : false,
        s_top : false,
        s_up : true,
        s_keyboardNode : false});
    updateVarsToUI();
});

for(let i=0; i<unselectedNotes.length;i++){
    unselectedNotes[i].addEventListener("click", _ => {
        [up] = control({
            s_bottom : false,
            s_top : false,
            s_up : false,
            s_keyboardNode : true});
        updateVarsToUI();    
});};


var triggerNotes = new Set(["s_bottom", "s_top", "s_up"]);
function reactiveUpdateOnMIDI(note, velocity){
    const noteSignal = 's_note' + note;
    const noteVelocity = velocity;
    const inputTemplate = {
        s_bottom : false,
        s_top : false,
        s_up : false,
        s_keyboardNode : false,
    };
    inputTemplate[noteSignal] = true;
    if(triggerNotes.has(noteSignal)){
        [up] = control(inputTemplate);
        updateVarsToUI();
    }
}

amOffBtn.click();
fmOffBtn.click();
lfoOffBtn.click();



