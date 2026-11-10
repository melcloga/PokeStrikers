#ifndef _PORT_FREECAM_H_
#define _PORT_FREECAM_H_

#ifdef __cplusplus
extern "C" {
#endif

// A free-fly camera for taking screenshots from any angle (F8 toggles it). The match carries on
// underneath; F3 freezes it. It starts from wherever the game camera is looking.
//
//   W A S D   fly      E / Q  up / down      Shift fast, Ctrl slow
//   hold the right mouse button and move the mouse to look      [ and ]  zoom (field of view)
//
// While it is on the keyboard is detached from player 1, so those keys steer the camera only.
// Not available in lockstep or online play, where a camera that is not the match's would
// desynchronise nothing but is not worth the risk.
void PortFreeCamToggle(void);
int  PortFreeCamActive(void);

#ifdef __cplusplus
}
#endif

#endif // _PORT_FREECAM_H_
