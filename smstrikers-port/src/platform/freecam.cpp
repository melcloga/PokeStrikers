// The free camera. See include/port/freecam.h.

#include "port/freecam.h"

#if !defined(PORT_USE_AURORA)

extern "C" void PortFreeCamToggle(void) {}
extern "C" int PortFreeCamActive(void) { return 0; }

#else

#include <cmath>
#include <cstdio>

#include <dolphin/pad.h>
#include <SDL3/SDL_keyboard.h>
#include <SDL3/SDL_mouse.h>
#include <SDL3/SDL_scancode.h>

#include "Game/Camera/BaseCamera.h"
#include "Game/Camera/CameraMan.h"
#include "NL/gl/glMatrix.h"
#include "NL/nlMath.h"
#include "port/lockstep.h"
#include "port/online.h"
#include "port/overlay.h"

namespace
{

class cFreeCamera : public cBaseCamera
{
public:
    cFreeCamera() { m_matView.SetIdentity(); nlVec3Set(m_pos, 0.0f, 0.0f, 0.0f); nlVec3Set(m_look, 0.0f, 0.0f, 1.0f); }
    virtual ~cFreeCamera() {}
    virtual eCameraType GetType() { return eCameraType_Debug; }
    virtual const nlMatrix4& GetViewMatrix() const { return m_matView; }
    virtual float GetFOV() const { return m_fov; }
    virtual const nlVector3& GetTargetPosition() const { return m_look; }
    virtual const nlVector3& GetCameraPosition() const { return m_pos; }

    void StartFrom(const cBaseCamera* from)
    {
        if (from != nullptr)
        {
            m_pos = from->GetCameraPosition();
            const nlVector3 t = from->GetTargetPosition();
            const float dx = t.x - m_pos.x, dy = t.y - m_pos.y, dz = t.z - m_pos.z;
            const float flat = sqrtf(dx * dx + dy * dy);
            if (flat > 1e-4f || fabsf(dz) > 1e-4f)
            {
                m_yaw = atan2f(dy, dx);
                m_pitch = atan2f(dz, flat);
            }
            m_fov = from->GetFOV();
        }
        if (m_fov < 5.0f || m_fov > 120.0f)
            m_fov = 45.0f;
        Rebuild();
    }

    virtual void Update(float dt)
    {
        if (dt <= 0.0f || dt > 0.25f)
            dt = 0.0166f;
        const bool* keys = SDL_GetKeyboardState(nullptr);

        // Look: only while the right button is held, so the mouse stays free for the menu otherwise.
        float mx = 0.0f, my = 0.0f;
        const SDL_MouseButtonFlags buttons = SDL_GetRelativeMouseState(&mx, &my);
        if ((buttons & SDL_BUTTON_RMASK) != 0 && !PortOverlayMenuOpen())
        {
            m_yaw -= mx * 0.0026f;
            m_pitch -= my * 0.0026f;
            const float lim = 1.553f; // 89 degrees
            if (m_pitch > lim) m_pitch = lim;
            if (m_pitch < -lim) m_pitch = -lim;
        }

        float speed = 14.0f;
        if (keys[SDL_SCANCODE_LSHIFT] || keys[SDL_SCANCODE_RSHIFT]) speed *= 4.0f;
        if (keys[SDL_SCANCODE_LCTRL] || keys[SDL_SCANCODE_RCTRL]) speed *= 0.2f;

        const float cp = cosf(m_pitch), sp = sinf(m_pitch), cy = cosf(m_yaw), sy = sinf(m_yaw);
        const float fx = cp * cy, fy = cp * sy, fz = sp;   // forward
        const float rx = sy, ry = -cy;                     // right
        float mvf = 0.0f, mvr = 0.0f, mvu = 0.0f;
        if (keys[SDL_SCANCODE_W]) mvf += 1.0f;
        if (keys[SDL_SCANCODE_S]) mvf -= 1.0f;
        if (keys[SDL_SCANCODE_D]) mvr += 1.0f;
        if (keys[SDL_SCANCODE_A]) mvr -= 1.0f;
        if (keys[SDL_SCANCODE_E]) mvu += 1.0f;
        if (keys[SDL_SCANCODE_Q]) mvu -= 1.0f;
        m_pos.x += (fx * mvf + rx * mvr) * speed * dt;
        m_pos.y += (fy * mvf + ry * mvr) * speed * dt;
        m_pos.z += (fz * mvf + mvu) * speed * dt;

        if (keys[SDL_SCANCODE_LEFTBRACKET]) m_fov += 30.0f * dt;
        if (keys[SDL_SCANCODE_RIGHTBRACKET]) m_fov -= 30.0f * dt;
        if (m_fov < 8.0f) m_fov = 8.0f;
        if (m_fov > 110.0f) m_fov = 110.0f;

        Rebuild();
    }

private:
    void Rebuild()
    {
        const float cp = cosf(m_pitch);
        m_look.x = m_pos.x + cp * cosf(m_yaw);
        m_look.y = m_pos.y + cp * sinf(m_yaw);
        m_look.z = m_pos.z + sinf(m_pitch);
        nlVector3 up;
        nlVec3Set(up, 0.0f, 0.0f, 1.0f);
        glMatrixLookAt(m_matView, m_pos, m_look, up);
    }

    nlMatrix4 m_matView;
    nlVector3 m_pos;
    nlVector3 m_look;
    float m_yaw = 0.0f, m_pitch = 0.0f, m_fov = 45.0f;
};

cFreeCamera s_cam;
bool s_active = false;

} // namespace

extern "C" int PortFreeCamActive(void) { return s_active ? 1 : 0; }

extern "C" void PortFreeCamToggle(void)
{
    if (s_active)
    {
        cCameraManager::Remove(s_cam);
        s_active = false;
        // The menu keeps the keyboard if it is open; otherwise the player gets it back.
        PADSetKeyboardActive(0, PortOverlayMenuOpen() ? FALSE : TRUE);
        fprintf(stderr, "FREECAM off\n");
        return;
    }
    if (g_simLockstep || PortOnlineActive())
        return;
    if (cCameraManager::PeekCamera() == nullptr)
        return;   // no match yet
    s_cam.StartFrom(cCameraManager::PeekCamera());
    cCameraManager::PushCamera(&s_cam);
    s_active = true;
    PADSetKeyboardActive(0, FALSE);
    fprintf(stderr, "FREECAM on\n");
}

#endif
