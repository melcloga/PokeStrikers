#include "NL/glx/glxLoadModel.h"
#include "port/endian.h"
#include "NL/nlWare.h"
#include "dolphin/os.h"
extern "C" {
unsigned long port_bmd_swap_headers(void*, unsigned long);
unsigned long port_skin_swap(void*);
unsigned long port_bmd_packet_count(unsigned long);
unsigned long port_bmd_stream_count(unsigned long);
void port_bmd_convert_packets(void*, const void*, unsigned long);
void port_bmd_convert_streams(void*, const void*, unsigned long);
void port_bmd_stream_sizes(void*, unsigned long, unsigned long);
void port_bmd_swap_indices(void*, unsigned long);
unsigned long port_bmd_model_count(unsigned long);
void port_bmd_convert_models(void*, const void*, unsigned long, unsigned long);
}
#include "NL/glx/glxMemory.h"
#include "NL/gl/glMemory.h"
#include "NL/gl/glModel.h"
#include "NL/gl/glState.h"
#include "NL/gl/glTexture.h"
#include "NL/gl/glUserData.h"
#include "NL/glx/glxDisplayList.h"
#include "NL/glx/glxTexture.h"
#include "NL/nlFile.h"
#include "NL/nlFileGC.h"
#include "NL/nlString.h"
#include "NL/nlDLRing.h"
#include "NL/nlMemory.h"
#include "NL/platvmath.h"
#include "Game/GL/GLInventory.h"
#include "Game/GL/GLTextureAnim.h"
#include "Game/GL/GLVertexAnim.h"
#include "Game/GL/GLMaterial.h"
#include "Game/GL/ShaderSkinMesh.h"
#include "Game/SAnim.h"
#include "Game/Sys/debug.h"
#include "dolphin/os/OSCache.h"
#include <map>
#include <math.h>
#include <set>
#include <string.h>
#include <string>
#include <vector>
#include <stdio.h>
#include <stdlib.h>

extern GLInventory glInventory;

static bool glIgnoreDuplicateModels;

static glModel* glxLoadModelFromMemory(char* data, int size, unsigned long* pNumModels, bool bLoadTextures);

// PORT (mod): STRIKERS_PITCH_UNIFY=the_palace/pitch[,other/name] gives that model's ground one planar texture mapping
// (left edge of the model's bounds is u=0, top edge v=0) and points every packet at the first packet's texture, so
// one replacement PNG of any size can paint the whole pitch with no tiling or mirroring.
static bool PortPitchUnifyMatch(unsigned long id)
{
    // Built in: the stadium pitches that are set up for one-file painting. STRIKERS_PITCH_UNIFY adds more
    // (comma separated); STRIKERS_PITCH_UNIFY=0 turns the built-in ones off.
    static const char* sEnv = getenv("STRIKERS_PITCH_UNIFY");
    if (sEnv != NULL && strcmp(sEnv, "0") == 0)
        return false;
    static const std::string sAll = std::string("the_palace/pitch,mario_stadium/newfield01") +
                                    ((sEnv != NULL && sEnv[0] != '\0') ? std::string(",") + sEnv : std::string());
    std::string list(sAll);
    size_t start = 0;
    while (start <= list.size())
    {
        size_t end = list.find(',', start);
        if (end == std::string::npos)
            end = list.size();
        std::string tok = list.substr(start, end - start);
        start = end + 1;
        if (tok.empty())
            continue;
        char* endp = NULL;
        unsigned long v = strtoul(tok.c_str(), &endp, 16);
        unsigned long h = (endp != NULL && *endp == '\0') ? v : nlStringLowerHash(tok.c_str());
        if (h == id)
            return true;
    }
    return false;
}

// PORT (mod): STRIKERS_PITCH_FILL=1 (with STRIKERS_PITCH_UNIFY) rebuilds each goal-end decal of the pitch model
// (the packets that carry a mask UV stream) as one flat rectangle in the same ground plane, so the ground there is
// plain pitch texture instead of the original odd-shaped patch with the underwater floor showing around it.
static void PortStoreBEf32(u8* q, float f)
{
    u32 v;
    memcpy(&v, &f, 4);
    q[0] = (u8)(v >> 24);
    q[1] = (u8)(v >> 16);
    q[2] = (u8)(v >> 8);
    q[3] = (u8)v;
}

static void PortPitchFill(glModel* pModel)
{
    const int n = (int)pModel->numPackets;
    glModelPacket* p = pModel->packets;
    for (int k = 0; k < n; k++, p = (glModelPacket*)((u8*)p + sizeof(glModelPacket)))
    {
        const glModelStream* pos = NULL;
        const glModelStream* col = NULL;
        const glModelStream* uv1 = NULL;
        const glModelStream* uvm = NULL;
        for (int s = 0; s < (int)p->numStreams; s++)
        {
            switch (p->streams[s].id)
            {
            case 0: pos = &p->streams[s]; break;
            case 2: col = &p->streams[s]; break;
            case 4: uv1 = &p->streams[s]; break;
            case 5: uvm = &p->streams[s]; break;
            }
        }
        if (pos == NULL || uvm == NULL || p->primType != 0 || p->indexBuffer == 0 || pos->stride < 12 || uvm->stride < 4
            || p->numVertices < 6 || p->numVertices > 300)
            continue;
        u16* idx = (u16*)p->indexBuffer;
        const int nv = (int)p->numVertices;
        u16 uniq[64];
        int nu = 0;
        for (int i = 0; i < nv && nu < 64; i++)
        {
            bool seen = false;
            for (int j = 0; j < nu; j++)
                if (uniq[j] == idx[i])
                    seen = true;
            if (!seen)
                uniq[nu++] = idx[i];
        }
        if (nu < 4)
            continue;
        float xmin = 1e30f, xmax = -1e30f, ymin = 1e30f, ymax = -1e30f;
        for (int j = 0; j < nu; j++)
        {
            const u8* pv = (const u8*)pos->address + (size_t)uniq[j] * pos->stride;
            const float x = port_bef32(pv), y = port_bef32(pv + 4);
            if (x < xmin) xmin = x;
            if (x > xmax) xmax = x;
            if (y < ymin) ymin = y;
            if (y > ymax) ymax = y;
        }
        // winding of the first real triangle
        float sign = 1.0f;
        for (int i = 0; i + 2 < nv; i += 3)
        {
            const u8* a = (const u8*)pos->address + (size_t)idx[i] * pos->stride;
            const u8* b = (const u8*)pos->address + (size_t)idx[i + 1] * pos->stride;
            const u8* c = (const u8*)pos->address + (size_t)idx[i + 2] * pos->stride;
            const float ar = (port_bef32(b) - port_bef32(a)) * (port_bef32(c + 4) - port_bef32(a + 4))
                           - (port_bef32(b + 4) - port_bef32(a + 4)) * (port_bef32(c) - port_bef32(a));
            if (ar > 1e-6f || ar < -1e-6f)
            {
                sign = ar > 0.0f ? 1.0f : -1.0f;
                break;
            }
        }
        // affine fit of the detail UV (stream 4) against x,y over the original vertices
        double ua = 0, ub = 0, uc = 0, va = 0, vb = 0, vc = 0;
        bool haveFit = false;
        if (uv1 != NULL && uv1->stride >= 4)
        {
            double sxx = 0, sxy = 0, sx = 0, syy = 0, sy = 0, sn = 0, sxu = 0, syu = 0, su = 0, sxv = 0, syv = 0, sv = 0;
            for (int j = 0; j < nu; j++)
            {
                const u8* pv = (const u8*)pos->address + (size_t)uniq[j] * pos->stride;
                const u8* pu = (const u8*)uv1->address + (size_t)uniq[j] * uv1->stride;
                const double x = port_bef32(pv), y = port_bef32(pv + 4);
                const double u = (double)(short)((pu[0] << 8) | pu[1]);
                const double v = (double)(short)((pu[2] << 8) | pu[3]);
                sxx += x * x; sxy += x * y; sx += x; syy += y * y; sy += y; sn += 1;
                sxu += x * u; syu += y * u; su += u; sxv += x * v; syv += y * v; sv += v;
            }
            const double m[3][3] = { { sxx, sxy, sx }, { sxy, syy, sy }, { sx, sy, sn } };
            const double det = m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
                             - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
                             + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]);
            if (det > 1e-9 || det < -1e-9)
            {
                auto solve = [&](double r0, double r1, double r2, double& A, double& B, double& C) {
                    double dA = r0 * (m[1][1] * m[2][2] - m[1][2] * m[2][1]) - m[0][1] * (r1 * m[2][2] - m[1][2] * r2) + m[0][2] * (r1 * m[2][1] - m[1][1] * r2);
                    double dB = m[0][0] * (r1 * m[2][2] - m[1][2] * r2) - r0 * (m[1][0] * m[2][2] - m[1][2] * m[2][0]) + m[0][2] * (m[1][0] * r2 - r1 * m[2][0]);
                    double dC = m[0][0] * (m[1][1] * r2 - r1 * m[2][1]) - m[0][1] * (m[1][0] * r2 - r1 * m[2][0]) + r0 * (m[1][0] * m[2][1] - m[1][1] * m[2][0]);
                    A = dA / det; B = dB / det; C = dC / det;
                };
                solve(sxu, syu, su, ua, ub, uc);
                solve(sxv, syv, sv, va, vb, vc);
                haveFit = true;
            }
        }
        // Only the left-hand patch has a hole: the main pitch has a rectangular notch cut out beside the half-disc
        // decal. The right-hand end is already whole, so it is left exactly as the game made it.
        if ((xmin + xmax) * 0.5f >= 0.0f)
            continue;
        const float rx0 = -20.9f;        // a hair into the half-disc (its visible edge is at about -20.7)
        const float rx1 = -18.7f;        // a hair into the main pitch
        const float ry0 = -4.2f, ry1 = 5.2f;

        // Convex hull of the original half-disc (monotone chain), so it can be redrawn with far fewer triangles and
        // leave room in the index list for the notch patch.
        int order[64];
        for (int j = 0; j < nu; j++)
            order[j] = j;
        auto px = [&](int j) { return port_bef32((const u8*)pos->address + (size_t)uniq[j] * pos->stride); };
        auto py = [&](int j) { return port_bef32((const u8*)pos->address + (size_t)uniq[j] * pos->stride + 4); };
        for (int a = 1; a < nu; a++)
            for (int b = a; b > 0 && (px(order[b]) < px(order[b - 1]) || (px(order[b]) == px(order[b - 1]) && py(order[b]) < py(order[b - 1]))); b--)
            {
                int t = order[b]; order[b] = order[b - 1]; order[b - 1] = t;
            }
        auto cross = [&](int o, int a, int b) {
            return (px(a) - px(o)) * (py(b) - py(o)) - (py(a) - py(o)) * (px(b) - px(o));
        };
        int hull[130];
        int hn = 0;
        for (int a = 0; a < nu; a++)
        {
            while (hn >= 2 && cross(hull[hn - 2], hull[hn - 1], order[a]) <= 1e-6f)
                hn--;
            hull[hn++] = order[a];
        }
        const int lowerEnd = hn + 1;
        for (int a = nu - 2; a >= 0; a--)
        {
            while (hn >= lowerEnd && cross(hull[hn - 2], hull[hn - 1], order[a]) <= 1e-6f)
                hn--;
            hull[hn++] = order[a];
        }
        hn--;
        bool onHull[64] = {};
        for (int a = 0; a < hn; a++)
            onHull[hull[a]] = true;
        int spare[4];
        int ns = 0;
        for (int j = 0; j < nu && ns < 4; j++)
            if (!onHull[j])
                spare[ns++] = j;
        if (ns < 4 || (hn - 2 + 2) * 3 > nv)
            continue;

        const float cx[4] = { rx0, rx1, rx1, rx0 };
        const float cy[4] = { ry0, ry0, ry1, ry1 };
        for (int j = 0; j < 4; j++)
        {
            const int s = spare[j];
            u8* pv = (u8*)pos->address + (size_t)uniq[s] * pos->stride;
            PortStoreBEf32(pv, cx[j]);
            PortStoreBEf32(pv + 4, cy[j]);
            PortStoreBEf32(pv + 8, 0.006f); // a hair above the ground: wins every depth test (no flicker) yet shifts lines by under a pixel
            u8* pm = (u8*)uvm->address + (size_t)uniq[s] * uvm->stride;
            pm[0] = 0; pm[1] = 24; pm[2] = 0; pm[3] = 24;
            if (haveFit && uv1 != NULL)
            {
                u8* pu = (u8*)uv1->address + (size_t)uniq[s] * uv1->stride;
                int u = (int)(ua * cx[j] + ub * cy[j] + uc);
                int v = (int)(va * cx[j] + vb * cy[j] + vc);
                if (u < -32768) u = -32768;
                if (u > 32767) u = 32767;
                if (v < -32768) v = -32768;
                if (v > 32767) v = 32767;
                pu[0] = (u8)((u >> 8) & 0xFF); pu[1] = (u8)(u & 0xFF);
                pu[2] = (u8)((v >> 8) & 0xFF); pu[3] = (u8)(v & 0xFF);
            }
        }
        // hull vertices are CCW; flip triangles if the original winding was clockwise
        int w = 0;
        for (int a = 1; a + 1 < hn; a++)
        {
            idx[w++] = uniq[hull[0]];
            idx[w++] = uniq[hull[sign < 0.0f ? a + 1 : a]];
            idx[w++] = uniq[hull[sign < 0.0f ? a : a + 1]];
        }
        const int rect[2][3] = { { 0, 1, 2 }, { 0, 2, 3 } };
        for (int a = 0; a < 2; a++)
        {
            idx[w++] = uniq[spare[rect[a][0]]];
            idx[w++] = uniq[spare[rect[a][sign < 0.0f ? 2 : 1]]];
            idx[w++] = uniq[spare[rect[a][sign < 0.0f ? 1 : 2]]];
        }
        while (w < nv)
        {
            idx[w] = idx[0];
            w++;
        }
        fprintf(stderr, "PITCHFILL packet=%d hull=%d notch x[%.2f,%.2f] y[%.2f,%.2f] winding=%.0f uvfit=%d\n", k, hn, rx0, rx1, ry0, ry1, sign, (int)haveFit);
    }
}

// PORT (mod): STRIKERS_HIDE_PACKETS=<model>:<packet>[+<packet>...][,<model>:...] makes the listed packets of a model
// draw nothing (every index points at one vertex, so all triangles collapse). <model> is a hex model hash or a name,
// e.g. the_palace/goal01:1+2. Used to switch off parts of a model (stray rods, notches) without touching the others.
static void PortHidePackets(glModel* pModel)
{
    // Built in: Pipeline Central's goal-end lift plates (they exist on one end only). Hidden at model level so it
    // holds however the world creates them. STRIKERS_HIDE_PACKETS adds more; =0 turns the built-in ones off.
    static const char* sEnv = getenv("STRIKERS_HIDE_PACKETS");
    if (sEnv != NULL && strcmp(sEnv, "0") == 0)
        return;
    static const std::string sAll = std::string("mario_stadium/lift03:0+1+2+3,mario_stadium/lift04:0+1+2+3") +
                                    ((sEnv != NULL && sEnv[0] != '\0') ? std::string(",") + sEnv : std::string());
    const std::string list(sAll);
    size_t start = 0;
    while (start <= list.size())
    {
        size_t end = list.find(',', start);
        if (end == std::string::npos)
            end = list.size();
        std::string tok = list.substr(start, end - start);
        start = end + 1;
        const size_t colon = tok.find(':');
        if (colon == std::string::npos)
            continue;
        const std::string name = tok.substr(0, colon);
        char* endp = NULL;
        unsigned long v = strtoul(name.c_str(), &endp, 16);
        unsigned long h = (endp != NULL && *endp == '\0') ? v : nlStringLowerHash(name.c_str());
        if (h != pModel->id)
            continue;
        const std::string pk = tok.substr(colon + 1);
        size_t a = 0;
        while (a <= pk.size())
        {
            size_t b = pk.find('+', a);
            if (b == std::string::npos)
                b = pk.size();
            const std::string num = pk.substr(a, b - a);
            a = b + 1;
            if (num.empty())
                continue;
            const int k = atoi(num.c_str());
            if (k < 0 || k >= (int)pModel->numPackets)
                continue;
            glModelPacket* p = (glModelPacket*)((u8*)pModel->packets + (size_t)k * sizeof(glModelPacket));
            if (p->indexBuffer == 0 || p->numVertices == 0)
                continue;
            u16* idx = (u16*)p->indexBuffer;
            for (int i = 0; i < (int)p->numVertices; i++)
                idx[i] = idx[0];
            fprintf(stderr, "HIDEPACKET model=%08x packet=%d nv=%d\n", (unsigned)pModel->id, k, (int)p->numVertices);
        }
    }
}

// PORT (mod): STRIKERS_GOAL_FIX=1 closes the broken-off notches in the Palace goal rims. The rim is one mesh (packet 0
// of the goal01 / goal05 models); each notch is a patch of irregular triangles. This swaps those triangles for
// whole faces built from the neighbouring intact vertices (the two curved-rim spans also get a new middle ring,
// stored in the vertices that the notch triangles no longer use). Generated offline from the shipped model data.
static const int kgoal05_tris[] = { 17, 31, 32, 10, 18, 10, 11, 31, 385, 376, 384, 23, 387, 23, 22, 376, 388, 32, 3, 19, 389, 19, 10, 32, 390, 0, 0, 0, 391, 0, 0, 0, 392, 0, 0, 0, 393, 0, 0, 0, 394, 0, 0, 0, 395, 0, 0, 0, 396, 0, 0, 0, 397, 0, 0, 0, 398, 0, 0, 0, 399, 0, 0, 0, 400, 0, 0, 0, 401, 0, 0, 0, 402, 0, 0, 0, 403, 0, 0, 0, 404, 0, 0, 0, 405, 0, 0, 0, 406, 0, 0, 0, 407, 0, 0, 0, 408, 0, 0, 0, 409, 0, 0, 0, 410, 0, 0, 0, 411, 0, 0, 0, 412, 0, 0, 0, 413, 0, 0, 0, 414, 0, 0, 0, 415, 0, 0, 0, 416, 0, 0, 0, 417, 0, 0, 0, 418, 0, 0, 0, 419, 0, 0, 0, 422, 30, 21, 41, 424, 41, 40, 30, 425, 33, 30, 40, 426, 40, 44, 33, 427, 21, 20, 296, 428, 296, 41, 21, 429, 0, 0, 0, 430, 0, 0, 0, 431, 0, 0, 0, 432, 0, 0, 0, 433, 0, 0, 0, 434, 0, 0, 0, 435, 0, 0, 0, 37, 40, 41, 55, 42, 55, 69, 40, 43, 50, 48, 47, 44, 47, 49, 50, 45, 56, 59, 66, 46, 66, 60, 56, 302, 41, 296, 36, 303, 36, 55, 41, 304, 0, 0, 0, 305, 0, 0, 0, 306, 0, 0, 0, 307, 0, 0, 0, 308, 0, 0, 0, 309, 0, 0, 0, 310, 0, 0, 0, 311, 0, 0, 0, 312, 0, 0, 0, 313, 0, 0, 0, 314, 0, 0, 0, 315, 0, 0, 0, 316, 0, 0, 0, 317, 0, 0, 0, 318, 0, 0, 0, 75, 84, 83, 106, 76, 105, 106, 90, 79, 106, 105, 84, 80, 90, 89, 105, 81, 109, 86, 85, 82, 93, 109, 110, 99, 85, 110, 109, 100, 110, 94, 93, 101, 265, 112, 88, 102, 100, 99, 112, 103, 88, 87, 265, 104, 112, 265, 100, 263, 84, 105, 110, 264, 105, 89, 94, 265, 110, 85, 84, 266, 94, 110, 105, 267, 121, 266, 265, 268, 266, 111, 100, 269, 265, 87, 121, 270, 100, 265, 266, 271, 268, 267, 127, 272, 128, 131, 267, 273, 127, 126, 268, 274, 267, 268, 128, 275, 83, 142, 269, 276, 106, 269, 134, 277, 269, 106, 83, 278, 134, 90, 106, 279, 145, 88, 112, 280, 270, 112, 99, 281, 112, 270, 145, 282, 99, 137, 270, 283, 0, 0, 0, 284, 0, 0, 0, 285, 0, 0, 0, 286, 0, 0, 0, 287, 0, 0, 0, 288, 0, 0, 0, 289, 0, 0, 0, 290, 0, 0, 0, 291, 0, 0, 0, 292, 0, 0, 0, 293, 0, 0, 0, 294, 0, 0, 0, 295, 0, 0, 0, 296, 0, 0, 0, 297, 0, 0, 0, 298, 0, 0, 0, 299, 0, 0, 0, 300, 0, 0, 0, 301, 0, 0, 0 };
static const int kgoal05_nTris = 123;
static const int kgoal05_verts[] = { 105, -70, -520, 322, 41, 41, -24, 171, 171, 171, 255, 542, 22, 106, -70, -520, 384, 41, 42, 23, 171, 171, 171, 255, 542, -888, 109, -134, -584, 314, -17, -18, -58, 171, 171, 171, 255, 542, 1019, 110, -75, -525, 314, 16, 16, -59, 171, 171, 171, 255, 542, 114, 112, -139, -590, 384, -41, -42, 23, 171, 171, 171, 255, 542, -888, 265, -139, -590, 322, -41, -42, -24, 171, 171, 171, 255, 542, 22, 266, -134, -584, 314, -17, -18, -58, 171, 171, 171, 255, 542, 114, 267, -75, -525, 392, 17, 17, 59, 171, 171, 171, 255, 542, 114, 268, -134, -584, 392, -18, -18, 58, 171, 171, 171, 255, 542, 1019, 269, -75, -525, 392, 17, 17, 59, 171, 171, 171, 255, 542, -984, 270, -134, -584, 392, -18, -18, 58, 171, 171, 171, 255, 542, -984 };
static const int kgoal05_nVerts = 11;
static const unsigned kgoal05_id = 0x67842b9cu;
static const int kgoal01_tris[] = { 42, 40, 41, 58, 49, 58, 71, 40, 50, 50, 48, 47, 51, 47, 49, 50, 52, 59, 62, 69, 53, 69, 63, 59, 273, 41, 56, 36, 274, 36, 58, 41, 275, 0, 0, 0, 276, 0, 0, 0, 277, 0, 0, 0, 278, 0, 0, 0, 279, 0, 0, 0, 280, 0, 0, 0, 281, 0, 0, 0, 282, 0, 0, 0, 283, 0, 0, 0, 284, 0, 0, 0, 285, 0, 0, 0, 286, 0, 0, 0, 287, 0, 0, 0, 288, 0, 0, 0, 289, 0, 0, 0, 84, 87, 86, 109, 85, 108, 109, 93, 88, 109, 108, 87, 89, 93, 92, 108, 90, 112, 89, 88, 91, 96, 112, 113, 108, 88, 113, 112, 109, 113, 97, 96, 110, 230, 115, 91, 111, 103, 102, 115, 112, 91, 90, 230, 113, 115, 230, 103, 234, 87, 108, 113, 235, 108, 92, 97, 236, 113, 88, 87, 237, 97, 113, 108, 238, 124, 231, 230, 239, 231, 114, 103, 240, 230, 90, 124, 241, 103, 230, 231, 242, 233, 232, 130, 243, 131, 134, 232, 244, 130, 129, 233, 245, 232, 233, 131, 246, 86, 145, 234, 247, 109, 234, 137, 248, 234, 109, 86, 249, 137, 93, 109, 250, 148, 91, 115, 251, 235, 115, 102, 252, 115, 235, 148, 253, 102, 140, 235, 254, 0, 0, 0, 255, 0, 0, 0, 256, 0, 0, 0, 257, 0, 0, 0, 258, 0, 0, 0, 259, 0, 0, 0, 260, 0, 0, 0, 261, 0, 0, 0, 262, 0, 0, 0, 263, 0, 0, 0, 264, 0, 0, 0, 265, 0, 0, 0, 266, 0, 0, 0, 267, 0, 0, 0, 268, 0, 0, 0, 269, 0, 0, 0, 270, 0, 0, 0, 271, 0, 0, 0, 272, 0, 0, 0 };
static const int kgoal01_nTris = 74;
static const int kgoal01_verts[] = { 108, 70, 520, 322, -41, -41, -24, 171, 171, 171, 255, 542, 22, 109, 70, 520, 384, -41, -42, 23, 171, 171, 171, 255, 542, -888, 112, 134, 584, 314, 17, 18, -58, 171, 171, 171, 255, 542, 1019, 113, 75, 525, 314, -16, -16, -59, 171, 171, 171, 255, 542, 114, 115, 139, 590, 384, 41, 42, 23, 171, 171, 171, 255, 542, -888, 230, 139, 590, 322, 41, 42, -24, 171, 171, 171, 255, 542, 22, 231, 134, 584, 314, 17, 18, -58, 171, 171, 171, 255, 542, 114, 232, 75, 525, 392, -17, -17, 59, 171, 171, 171, 255, 542, 114, 233, 134, 584, 392, 18, 18, 58, 171, 171, 171, 255, 542, 1019, 234, 75, 525, 392, -17, -17, 59, 171, 171, 171, 255, 542, -984, 235, 134, 584, 392, 18, 18, 58, 171, 171, 171, 255, 542, -984 };
static const int kgoal01_nVerts = 11;
static const unsigned kgoal01_id = 0x67842b98u;

static void PortStoreBE16(u8* q, int v)
{
    q[0] = (u8)((v >> 8) & 0xFF);
    q[1] = (u8)(v & 0xFF);
}

static void PortGoalFixOne(glModel* pModel, const int* tris, int nTris, const int* verts, int nVerts)
{
    if (pModel->numPackets < 1)
        return;
    glModelPacket* p = pModel->packets;
    const glModelStream* pos = NULL;
    const glModelStream* nrm = NULL;
    const glModelStream* col = NULL;
    const glModelStream* uv = NULL;
    for (int s = 0; s < (int)p->numStreams; s++)
    {
        switch (p->streams[s].id)
        {
        case 0: pos = &p->streams[s]; break;
        case 1: nrm = &p->streams[s]; break;
        case 2: col = &p->streams[s]; break;
        case 3: uv = &p->streams[s]; break;
        }
    }
    if (pos == NULL || nrm == NULL || col == NULL || uv == NULL || p->indexBuffer == 0 || pos->stride != 6 || nrm->stride != 3
        || col->stride != 4 || uv->stride != 4)
        return;
    const int nv = (int)p->numVertices;
    if (nv < 3)
        return;
    u16* idx = (u16*)p->indexBuffer;
    for (int i = 0; i < nVerts; i++)
    {
        const int* e = verts + i * 14;
        const int v = e[0];
        u8* pp = (u8*)pos->address + (size_t)v * 6;
        PortStoreBE16(pp, e[1]); PortStoreBE16(pp + 2, e[2]); PortStoreBE16(pp + 4, e[3]);
        u8* pn = (u8*)nrm->address + (size_t)v * 3;
        pn[0] = (u8)(s8)e[4]; pn[1] = (u8)(s8)e[5]; pn[2] = (u8)(s8)e[6];
        u8* pc = (u8*)col->address + (size_t)v * 4;
        pc[0] = (u8)e[7]; pc[1] = (u8)e[8]; pc[2] = (u8)e[9]; pc[3] = (u8)e[10];
        u8* pu = (u8*)uv->address + (size_t)v * 4;
        PortStoreBE16(pu, e[11]); PortStoreBE16(pu + 2, e[12]);
    }
    int written = 0;
    for (int i = 0; i < nTris; i++)
    {
        const int* e = tris + i * 4;
        const int k = e[0];
        if (k < 0 || (k + 1) * 3 > nv)
            continue;
        idx[k * 3] = (u16)e[1];
        idx[k * 3 + 1] = (u16)e[2];
        idx[k * 3 + 2] = (u16)e[3];
        written++;
    }
    fprintf(stderr, "GOALFIX model=%08x tris=%d verts=%d\n", (unsigned)pModel->id, written, nVerts);
}

static void PortGoalFix(glModel* pModel)
{
    static const bool bOn = getenv("STRIKERS_GOAL_FIX") != NULL;
    if (!bOn)
        return;
    if (pModel->id == kgoal05_id)
        PortGoalFixOne(pModel, kgoal05_tris, kgoal05_nTris, kgoal05_verts, kgoal05_nVerts);
    else if (pModel->id == kgoal01_id)
        PortGoalFixOne(pModel, kgoal01_tris, kgoal01_nTris, kgoal01_verts, kgoal01_nVerts);
}


// PORT (mod): Mario Stadium back wall (exteriorbuildtopwall02). Its two side panels are mirror copies that keep the
// same UVs, so a logo painted on the texture reads correctly on one panel and mirrored on the other. Mirror U
// inside the panel's own range (0..kPanelU, 0..0.582 of the texture) for the vertices of the flat, front-facing
// panel on the +X side so both read left to right. STRIKERS_BACKWALL_FIX=0 turns it off.
static void PortBackWallMirror(glModel* pModel)
{
    static const char* sOff = getenv("STRIKERS_BACKWALL_FIX");
    if (sOff != NULL && sOff[0] == '0')
        return;
    if (nlStringLowerHash("mario_stadium/exteriorbuildtopwall02") != pModel->id)
        return;
    const int kPanelU = 596; // 0.582 * 1024, the inner edge of the panel in U
    std::set<uintptr_t> done;
    int flipped = 0;
    glModelPacket* p = pModel->packets;
    for (int k = 0; k < (int)pModel->numPackets; k++, p = (glModelPacket*)((u8*)p + sizeof(glModelPacket)))
    {
        if (p->indexBuffer == 0)
            continue;
        const glModelStream* pos = NULL;
        const glModelStream* nrm = NULL;
        const glModelStream* uv = NULL;
        for (int s = 0; s < (int)p->numStreams; s++)
        {
            if (p->streams[s].id == 0)
                pos = &p->streams[s];
            else if (p->streams[s].id == 1)
                nrm = &p->streams[s];
            else if (p->streams[s].id == 3)
                uv = &p->streams[s];
        }
        if (pos == NULL || nrm == NULL || uv == NULL || nrm->stride < 3 || uv->stride < 4 || (pos->stride != 6 && pos->stride < 12))
            continue;
        const u16* idx = (const u16*)p->indexBuffer;
        for (int i = 0; i < (int)p->numVertices; i++)
        {
            const u8* pv = (const u8*)pos->address + (size_t)idx[i] * pos->stride;
            const double x = (pos->stride == 6) ? (double)(s16)port_be16(pv) / 256.0 : (double)port_bef32(pv);
            const double z = (pos->stride == 6) ? (double)(s16)port_be16(pv + 4) / 256.0 : (double)port_bef32(pv + 8);
            if (x <= 0.0)
                continue;
            u8* pu = (u8*)uv->address + (size_t)idx[i] * uv->stride;
            // The flat side panel and the rounded corner next to it share one planar mapping, u = 2.2705 - 0.0836 x
            // and v = 0.4622 - 0.0663 z. A few edge vertices (the outer lip and the bottom of the corner) were
            // authored slightly off that plane, so anything at x >= 19.9 whose U lies inside the panel's own range
            // (0..0.6) is mirrored with it. The window frame's own islands are left alone. Checked offline: every
            // triangle is either entirely inside this set or entirely outside it.
            const double uu = (double)(s16)port_be16(pu) / 1024.0;
            const double vv = (double)(s16)port_be16(pu + 2) / 1024.0;
            const bool planar = fabs(uu - (2.2705 - 0.0836 * x)) <= 0.004 && fabs(vv - (0.4622 - 0.0663 * z)) <= 0.004;
            if (!planar && !(x >= 19.9 && uu <= 0.6))
                continue;
            if (!done.insert((uintptr_t)pu).second)
                continue;
            const int u = (s16)port_be16(pu);
            PortStoreBE16(pu, kPanelU - u);
            flipped++;
        }
    }
    fprintf(stderr, "BACKWALL mirrored %d UVs\n", flipped);
}

// PORT (mod): sign boards that read backwards. The stadium builds its four sign walls as mirror copies of each
// other but keeps the UVs, so an ad reads correctly on one wall and mirrored on the other (and mirrored on the
// opposite side of the field). For every packet that uses one of the listed ad textures this works out, from the
// packet's own vertices and normals, whether U runs left to right as seen from the front, and if not mirrors U
// inside its own tile so the texture reads correctly from everywhere. STRIKERS_SIGN_FIX=0 turns it off. To cover
// another stadium, add the hash range of its ad textures (the glt names, sequential in the Palace) to the table.
struct PortSignRange
{
    u32 lo;
    u32 hi;
};
static const PortSignRange kPortSignRanges[] = {
    { 0x82D5B11Fu, 0x82D5B126u }, // the_palace: eight 256x64 ad textures
};

static bool PortSignTexture(u32 hash)
{
    for (size_t i = 0; i < sizeof(kPortSignRanges) / sizeof(kPortSignRanges[0]); i++)
    {
        if (hash >= kPortSignRanges[i].lo && hash <= kPortSignRanges[i].hi)
            return true;
    }
    return false;
}

static void PortSignOrient(glModel* pModel)
{
    static const bool bOff = getenv("STRIKERS_SIGN_FIX") != NULL && getenv("STRIKERS_SIGN_FIX")[0] == '0';
    if (bOff)
        return;

    // One entry per distinct vertex of the ad boards, keyed by where its UV lives so packets that share a vertex
    // are tied together.
    struct SignVertex
    {
        u8* uv;
        double x, y, nx, ny, nz, u;
        int parent;
    };
    std::vector<SignVertex> verts;
    std::map<uintptr_t, int> byKey;
    auto find = [&](int i) {
        while (verts[i].parent != i)
        {
            verts[i].parent = verts[verts[i].parent].parent;
            i = verts[i].parent;
        }
        return i;
    };

    const int n = (int)pModel->numPackets;
    glModelPacket* p = pModel->packets;
    for (int k = 0; k < n; k++, p = (glModelPacket*)((u8*)p + sizeof(glModelPacket)))
    {
        if (!PortSignTexture((u32)p->state.texture[0]) || p->indexBuffer == 0)
            continue;
        const glModelStream* pos = NULL;
        const glModelStream* nrm = NULL;
        const glModelStream* uv = NULL;
        for (int s = 0; s < (int)p->numStreams; s++)
        {
            if (p->streams[s].id == 0)
                pos = &p->streams[s];
            else if (p->streams[s].id == 1)
                nrm = &p->streams[s];
            else if (p->streams[s].id == 3)
                uv = &p->streams[s];
        }
        const int nv = (int)p->numVertices;
        if (pos == NULL || nrm == NULL || uv == NULL || nrm->stride < 3 || uv->stride < 4 || (pos->stride != 6 && pos->stride < 12) ||
            nv < 3)
            continue;
        const u16* idx = (const u16*)p->indexBuffer;

        std::vector<int> ids(nv);
        for (int i = 0; i < nv; i++)
        {
            u8* pu = (u8*)uv->address + (size_t)idx[i] * uv->stride;
            auto it = byKey.find((uintptr_t)pu);
            if (it != byKey.end())
            {
                ids[i] = it->second;
                continue;
            }
            SignVertex v;
            v.uv = pu;
            const u8* pv = (const u8*)pos->address + (size_t)idx[i] * pos->stride;
            if (pos->stride == 6)
            {
                v.x = (double)(s16)port_be16(pv) / 256.0;
                v.y = (double)(s16)port_be16(pv + 2) / 256.0;
            }
            else
            {
                v.x = port_bef32(pv);
                v.y = port_bef32(pv + 4);
            }
            const s8* pn = (const s8*)((const u8*)nrm->address + (size_t)idx[i] * nrm->stride);
            v.nx = pn[0];
            v.ny = pn[1];
            v.nz = pn[2];
            v.u = (double)(s16)port_be16(pu) / 1024.0;
            v.parent = (int)verts.size();
            ids[i] = v.parent;
            byKey[(uintptr_t)pu] = v.parent;
            verts.push_back(v);
        }
        // Tie the three corners of every triangle together. primType 1 is a strip, anything else a plain list.
        const bool strip = p->primType == 1;
        for (int i = 0; i + 2 < nv; i += (strip ? 1 : 3))
        {
            const int r0 = find(ids[i]);
            const int r1 = find(ids[i + 1]);
            const int r2 = find(ids[i + 2]);
            verts[r1].parent = r0;
            verts[find(r2)].parent = r0;
        }
    }

    // Each connected piece of board is judged on its own: is U running left to right as the viewer sees it?
    struct Piece
    {
        double nx = 0, ny = 0, nz = 0, um = 0, px = 0, py = 0, dx = 0, dy = 0;
        int count = 0;
    };
    std::map<int, Piece> pieces;
    for (size_t i = 0; i < verts.size(); i++)
    {
        Piece& pc = pieces[find((int)i)];
        pc.nx += verts[i].nx;
        pc.ny += verts[i].ny;
        pc.nz += verts[i].nz;
        pc.um += verts[i].u;
        pc.px += verts[i].x;
        pc.py += verts[i].y;
        pc.count++;
    }
    for (std::map<int, Piece>::iterator it = pieces.begin(); it != pieces.end(); ++it)
    {
        it->second.um /= it->second.count;
        it->second.px /= it->second.count;
        it->second.py /= it->second.count;
    }
    for (size_t i = 0; i < verts.size(); i++)
    {
        Piece& pc = pieces[find((int)i)];
        pc.dx += (verts[i].u - pc.um) * (verts[i].x - pc.px);
        pc.dy += (verts[i].u - pc.um) * (verts[i].y - pc.py);
    }
    int flipped = 0;
    for (std::map<int, Piece>::iterator it = pieces.begin(); it != pieces.end(); ++it)
    {
        const Piece& pc = it->second;
        const double nl = sqrt(pc.nx * pc.nx + pc.ny * pc.ny + pc.nz * pc.nz);
        if (nl < 1e-6 || fabs(pc.nz / nl) > 0.8) // not a board facing the pitch
            continue;
        const double nx = pc.nx / nl;
        const double ny = pc.ny / nl;
        // The viewer faces the board, looking along -normal with +Z up, so their right-hand direction is (-ny, nx).
        if (pc.dx * -ny + pc.dy * nx >= 0.0)
            continue; // already reads left to right
        for (size_t i = 0; i < verts.size(); i++)
        {
            if (find((int)i) != it->first)
                continue;
            // u -> 1 - u for every vertex of the piece. The texture repeats, so the whole-tile offset for
            // boards that started at -1 changes nothing.
            int ui = 1024 - (int)(s16)port_be16(verts[i].uv);
            if (ui < -32768) ui = -32768;
            if (ui > 32767) ui = 32767;
            verts[i].uv[0] = (u8)((ui >> 8) & 0xFF);
            verts[i].uv[1] = (u8)(ui & 0xFF);
        }
        flipped++;
    }
    if (flipped > 0)
        fprintf(stderr, "SIGNFIX model=%08x board pieces flipped=%d\n", (unsigned)pModel->id, flipped);
}

static void PortPitchUnify(glModel* pModel)
{
    if (!PortPitchUnifyMatch(pModel->id))
        return;
    const int n = (int)pModel->numPackets;
    if (n <= 0)
        return;
    {
        static const bool bFill = getenv("STRIKERS_PITCH_FILL") != NULL;
        if (bFill)
            PortPitchFill(pModel);
    }

    float xmin = 1e30f, xmax = -1e30f, ymin = 1e30f, ymax = -1e30f;
    int rewritten = 0;
    for (int pass = 0; pass < 2; pass++)
    {
        glModelPacket* p = pModel->packets;
        for (int k = 0; k < n; k++, p = (glModelPacket*)((u8*)p + sizeof(glModelPacket)))
        {
            const glModelStream* pos = NULL;
            const glModelStream* uv = NULL;
            for (int s = 0; s < (int)p->numStreams; s++)
            {
                if (p->streams[s].id == 0)
                    pos = &p->streams[s];
                else if (p->streams[s].id == 3)
                    uv = &p->streams[s];
            }
            if (pos == NULL || uv == NULL || p->indexBuffer == 0 || pos->stride < 12 || uv->stride < 4)
                continue;
            const u16* idx = (const u16*)p->indexBuffer;
            for (int i = 0; i < (int)p->numVertices; i++)
            {
                const u8* pv = (const u8*)pos->address + (size_t)idx[i] * pos->stride;
                const float x = port_bef32(pv);
                const float y = port_bef32(pv + 4);
                if (pass == 0)
                {
                    if (x < xmin) xmin = x;
                    if (x > xmax) xmax = x;
                    if (y < ymin) ymin = y;
                    if (y > ymax) ymax = y;
                }
                else
                {
                    float u = (x - xmin) / (xmax - xmin) * 1024.0f;
                    float v = (ymax - y) / (ymax - ymin) * 1024.0f;
                    int ui = (int)(u + 0.5f);
                    int vi = (int)(v + 0.5f);
                    if (ui < 0) ui = 0;
                    if (ui > 1024) ui = 1024;
                    if (vi < 0) vi = 0;
                    if (vi > 1024) vi = 1024;
                    // Snap the vertex onto the UV grid (1/1024 of the model) so neighbouring pieces of ground agree exactly.
                    PortStoreBEf32((u8*)pos->address + (size_t)idx[i] * pos->stride, xmin + (float)ui / 1024.0f * (xmax - xmin));
                    PortStoreBEf32((u8*)pos->address + (size_t)idx[i] * pos->stride + 4, ymax - (float)vi / 1024.0f * (ymax - ymin));
                    u8* pu = (u8*)uv->address + (size_t)idx[i] * uv->stride;
                    pu[0] = (u8)(ui >> 8);
                    pu[1] = (u8)ui;
                    pu[2] = (u8)(vi >> 8);
                    pu[3] = (u8)vi;
                    rewritten++;
                }
            }
        }
        if (pass == 0 && (!(xmax > xmin) || !(ymax > ymin)))
            return;
    }

    glModelPacket* first = pModel->packets;
    glModelPacket* p = first;
    for (int k = 0; k < n; k++, p = (glModelPacket*)((u8*)p + sizeof(glModelPacket)))
        p->state.texture[0] = first->state.texture[0];

    fprintf(stderr, "PITCHUNIFY model=%08x packets=%d vertices=%d bounds x[%.2f,%.2f] y[%.2f,%.2f] texture=%08x\n",
            (unsigned)pModel->id, n, rewritten, xmin, xmax, ymin, ymax, (unsigned)first->state.texture[0]);
}


// PORT (mod): Pipeline Central's field is newfield01 (see PortPitchUnify) but it has a hole at the left goal, and the
// goal floors / a corner plate piece sit at the ends. This gives those pieces the same world-space planar mapping
// and the same texture as the field model, so the whole playing area (behind the goals too) is one picture.
// Each entry: model name hash, packet mask (bit k = packet k), world transform of its single instance (2x2 diagonal
// signs and translation, from the .wld).
struct PortFieldExtra
{
    const char* name;
    unsigned packetMask;
    float sx, sy, tx, ty;
    float zset; // model-space height to flatten the packet to (1000 = leave as is)
};
static const PortFieldExtra kPortFieldExtras[] = {
    { "mario_stadium/netshadow_01", 0x7u, -1.0f, -1.0f, -20.2149f, 3.7794f, 1000.0f },
    { "mario_stadium/goalpost_floor01", 0x1u, 1.0f, 1.0f, -22.8025f, 0.0f, 1000.0f },
    { "mario_stadium/goalpost_floor02", 0x1u, 1.0f, 1.0f, 22.8026f, 0.0f, 1000.0f },
    { "mario_stadium/object22", 0x1u, -1.0f, -1.0f, -0.0194f, 0.0f, 1000.0f },
    { "mario_stadium/netshadow_02", 0x1u, -1.0f, -1.0f, 22.6817f, 0.4673f, 1000.0f },
    { "mario_stadium/pitchsurrounding03", 0x10u, -1.0f, -1.0f, 1.0266f, -13.3978f, 0.0f },
    { "mario_stadium/pitchsurrounding05", 0x10u, -1.0f, -1.0f, 1.0266f, 13.3141f, 0.0f },
};

// PORT (mod): Pipeline Central's pitch has rectangular cut-outs along both sideline rings where the recessed vent
// grates sit (and two small drain holes). Each cut-out is covered with a flat rectangle of the field's own picture, a
// hair above the ground, so the ring reads as one surface and the painted skyline runs straight across the vents.
// The rectangle is written into the vent model's own grate packet (packet 2), reusing its vertices. The rectangles
// are in world units (x0, x1, y0, y1). STRIKERS_VENT_COVER=0 turns it off.
struct PortVentRect
{
    float x0, x1, y0, y1;
};
struct PortVentModel
{
    const char* name;
    float sx, sy, tx, ty, tz;
    int numRects;
    PortVentRect rects[4];
};
static const PortVentModel kPortVentModels[] = {
    { "mario_stadium/pitchsurrounding02", 1.0f, 1.0f, -11.4331f, 9.9027f, -0.3158f, 2,
      { { -12.29f, -11.19f, 12.56f, 14.24f }, { -6.77f, -2.91f, 12.56f, 14.24f } } },
    { "mario_stadium/pitchsurrounding04", -1.0f, -1.0f, -11.4331f, -9.8847f, -0.3158f, 1,
      { { -10.92f, -5.66f, -13.81f, -12.14f } } },
    { "mario_stadium/pitchsurrounding05", -1.0f, -1.0f, 1.0266f, 13.3141f, -0.0019f, 4,
      { { 2.91f, 5.39f, 12.56f, 14.28f }, { 7.04f, 10.92f, 12.50f, 14.28f }, { -1.25f, -0.90f, 12.60f, 13.10f }, { 0.88f, 1.25f, 12.60f, 13.10f } } },
    { "mario_stadium/pitchsurrounding03", -1.0f, -1.0f, 1.0266f, -13.3978f, -0.0019f, 4,
      { { 2.91f, 5.39f, -13.81f, -12.14f }, { 7.04f, 10.92f, -13.81f, -12.14f }, { -1.28f, -0.90f, -12.67f, -12.18f }, { 0.88f, 1.25f, -12.67f, -12.18f } } },
};

static void PortVentCover(glModel* pModel)
{
    static const char* sOff = getenv("STRIKERS_VENT_COVER");
    if (sOff != NULL && sOff[0] == '0')
        return;
    const PortVentModel* e = NULL;
    for (size_t i = 0; i < sizeof(kPortVentModels) / sizeof(kPortVentModels[0]); i++)
    {
        if (nlStringLowerHash(kPortVentModels[i].name) == pModel->id)
        {
            e = &kPortVentModels[i];
            break;
        }
    }
    if (e == NULL || pModel->numPackets < 3)
        return;
    glModelPacket* p = (glModelPacket*)((u8*)pModel->packets + (size_t)2 * sizeof(glModelPacket));
    if (p->indexBuffer == 0)
        return;
    const glModelStream* pos = NULL;
    const glModelStream* nrm = NULL;
    const glModelStream* col = NULL;
    const glModelStream* uv = NULL;
    for (int st = 0; st < (int)p->numStreams; st++)
    {
        if (p->streams[st].id == 0)
            pos = &p->streams[st];
        else if (p->streams[st].id == 1)
            nrm = &p->streams[st];
        else if (p->streams[st].id == 2)
            col = &p->streams[st];
        else if (p->streams[st].id == 3)
            uv = &p->streams[st];
    }
    if (pos == NULL || uv == NULL || pos->stride != 6 || uv->stride < 4)
        return;
    u16* idx = (u16*)p->indexBuffer;
    const int nIdx = (int)p->numVertices;
    const bool strip = p->primType == 1;

    // Distinct vertex slots the packet already owns, in order of first use.
    std::vector<u16> slots;
    for (int i = 0; i < nIdx; i++)
    {
        bool seen = false;
        for (size_t j = 0; j < slots.size(); j++)
            if (slots[j] == idx[i]) { seen = true; break; }
        if (!seen)
            slots.push_back(idx[i]);
    }
    const int need = e->numRects * 4;
    const int entries = strip ? (e->numRects * 4 + (e->numRects - 1) * 2) : e->numRects * 6;
    if ((int)slots.size() < need || nIdx < entries)
    {
        fprintf(stderr, "VENTCOVER model=%08x too small (slots %d need %d, entries %d need %d)\n", (unsigned)pModel->id,
                (int)slots.size(), need, nIdx, entries);
        return;
    }

    const float xmin = -16.590908f, xmax = 16.590902f, ymin = -14.074756f, ymax = 14.519859f;
    const float zloc = 0.006f - e->tz;
    // The field pieces draw the picture with a second (detail) layer on UV stream 4. The grate packet has no such
    // stream, so a new stream array with a detail-UV buffer is made for it; without the layer the patch renders black.
    int maxIdx = 0;
    for (int i = 0; i < nIdx; i++)
        if ((int)idx[i] > maxIdx)
            maxIdx = idx[i];
    u8* dbuf = (u8*)calloc((size_t)(maxIdx + 1), 4);
    glModelStream* nst = (glModelStream*)calloc((size_t)p->numStreams + 1, sizeof(glModelStream));
    if (dbuf == NULL || nst == NULL)
        return;
    std::vector<u16> out;
    for (int r = 0; r < e->numRects; r++)
    {
        const PortVentRect& rc = e->rects[r];
        // corners in order BL, BR, TL, TR (world)
        const float wxs[4] = { rc.x0, rc.x1, rc.x0, rc.x1 };
        const float wys[4] = { rc.y0, rc.y0, rc.y1, rc.y1 };
        u16 v[4];
        for (int c = 0; c < 4; c++)
        {
            v[c] = slots[(size_t)r * 4 + c];
            const float lx = e->sx * (wxs[c] - e->tx);
            const float ly = e->sy * (wys[c] - e->ty);
            u8* pv = (u8*)pos->address + (size_t)v[c] * pos->stride;
            PortStoreBE16(pv, (int)floorf(lx * 256.0f + 0.5f));
            PortStoreBE16(pv + 2, (int)floorf(ly * 256.0f + 0.5f));
            PortStoreBE16(pv + 4, (int)floorf(zloc * 256.0f + 0.5f));
            const float u = (wxs[c] / 1.5f - xmin) / (xmax - xmin) * 1024.0f;
            const float vv = (ymax - (wys[c] + 0.1717f)) / (ymax - ymin) * 1024.0f;
            u8* pu = (u8*)uv->address + (size_t)v[c] * uv->stride;
            PortStoreBE16(pu, (int)floorf(u + 0.5f));
            PortStoreBE16(pu + 2, (int)floorf(vv + 0.5f));
            {
                const float xm = wxs[c] / 1.5f, ym = wys[c] + 0.1717f;
                const int du = (int)floorf((0.4380f * xm + 7.2645f) * 1024.0f + 0.5f);
                const int dv = (int)floorf((-0.1150f * ym - 2.7295f) * 1024.0f + 0.5f);
                u8* pd = dbuf + (size_t)v[c] * 4;
                PortStoreBE16(pd, du);
                PortStoreBE16(pd + 2, dv);
            }
            if (col != NULL && col->stride >= 4)
            {
                u8* pc = (u8*)col->address + (size_t)v[c] * col->stride;
                pc[0] = pc[1] = pc[2] = pc[3] = 255;
            }
            if (nrm != NULL && nrm->stride >= 3)
            {
                u8* pn = (u8*)nrm->address + (size_t)v[c] * nrm->stride;
                pn[0] = 0; pn[1] = 0; pn[2] = 64;
            }
        }
        if (strip)
        {
            if (r > 0)
            {
                out.push_back(out.back());
                out.push_back(v[0]);
            }
            out.push_back(v[0]); out.push_back(v[1]); out.push_back(v[2]); out.push_back(v[3]);
        }
        else
        {
            out.push_back(v[0]); out.push_back(v[1]); out.push_back(v[3]);
            out.push_back(v[0]); out.push_back(v[3]); out.push_back(v[2]);
        }
    }
    // Anything left over collapses onto the first vertex.
    for (int i = 0; i < nIdx; i++)
        idx[i] = (i < (int)out.size()) ? out[(size_t)i] : out[0];
    for (int st = 0; st < (int)p->numStreams; st++)
        nst[st] = p->streams[st];
    nst[p->numStreams].address = (uintptr_t)dbuf;
    nst[p->numStreams].id = 4;
    nst[p->numStreams].stride = 4;
    nst[p->numStreams].beData = uv->beData;
    nst[p->numStreams].dataSize = (u32)((maxIdx + 1) * 4);
    p->streams = nst;
    p->numStreams = (u8)(p->numStreams + 1);
    p->state.texturestate = 0x12b00000ULL;
    p->state.texconfig = 0x03;
    p->state.texture[0] = (uintptr_t)0xf406f013u;
    p->state.texture[1] = (uintptr_t)0x5c5698b2u;
    for (int t = 2; t < 6; t++)
        p->state.texture[t] = (uintptr_t)0xffffffffu;
    fprintf(stderr, "VENTCOVER model=%08x rects=%d\n", (unsigned)pModel->id, e->numRects);
}

// PORT (mod): the two corner plate pieces (packet 4) of Pipeline Central's right-end ring use a lit-plate texture with a
// bevel layer. They are given the same state as the ring floor beside them (packet 3) so they read as plain ring floor.
static void PortRingPlates(glModel* pModel)
{
    static const char* sOff = getenv("STRIKERS_FIELD_EXTRAS");
    if (sOff != NULL && strcmp(sOff, "0") == 0)
        return;
    if (nlStringLowerHash("mario_stadium/pitchsurrounding03") != pModel->id &&
        nlStringLowerHash("mario_stadium/pitchsurrounding05") != pModel->id)
        return;
    if (pModel->numPackets < 5)
        return;
    glModelPacket* ring = (glModelPacket*)((u8*)pModel->packets + (size_t)3 * sizeof(glModelPacket));
    glModelPacket* plate = (glModelPacket*)((u8*)pModel->packets + (size_t)4 * sizeof(glModelPacket));
    uintptr_t mtx = plate->state.matrix;
    plate->state = ring->state;
    plate->state.matrix = mtx;
    fprintf(stderr, "RINGPLATE model=%08x\n", (unsigned)pModel->id);
}


// PORT (mod): the stock field pieces are tinted warm (vertex colour 218,199,189), which would turn a white painted
// field peach. For Pipeline Central's field the tint is set to neutral so the picture shows as painted.
// STRIKERS_FIELD_TINT=1 keeps the stock tint.
static void PortFieldNeutral(glModel* pModel)
{
    static const char* sKeep = getenv("STRIKERS_FIELD_TINT");
    if (sKeep != NULL && sKeep[0] == '1')
        return;
    if (nlStringLowerHash("mario_stadium/newfield01") != pModel->id)
        return;
    int n = 0;
    for (int k = 0; k < (int)pModel->numPackets; k++)
    {
        glModelPacket* p = (glModelPacket*)((u8*)pModel->packets + (size_t)k * sizeof(glModelPacket));
        if (p->indexBuffer == 0)
            continue;
        const u16* idx = (const u16*)p->indexBuffer;
        for (int st = 0; st < (int)p->numStreams; st++)
        {
            if (p->streams[st].id != 2 || p->streams[st].stride < 4)
                continue;
            for (int i = 0; i < (int)p->numVertices; i++)
            {
                u8* pc = (u8*)p->streams[st].address + (size_t)idx[i] * p->streams[st].stride;
                pc[0] = 255; pc[1] = 255; pc[2] = 255; pc[3] = 255;
            }
            n++;
        }
    }
    fprintf(stderr, "FIELDNEUTRAL model=%08x packets=%d\n", (unsigned)pModel->id, n);
}

// PORT (mod): Pipeline Central's two goals share one net texture and one frame texture, so a texture pack could only
// recolour both alike. The right goal's net (netmesh) and frame (marionet05) are pointed at two otherwise unused textures
// that ship in the same stadium file, so each goal can be painted on its own. STRIKERS_GOAL_SPLIT=0 turns it off.
static void PortGoalSplit(glModel* pModel)
{
    static const char* sOff = getenv("STRIKERS_GOAL_SPLIT");
    if (sOff != NULL && strcmp(sOff, "0") == 0)
        return;
    u32 spare = 0;
    if (nlStringLowerHash("mario_stadium/netmesh") == pModel->id)
        spare = 0x88b56905u;
    else if (nlStringLowerHash("mario_stadium/marionet05") == pModel->id)
        spare = 0x9f6289d7u;
    else
        return;
    for (int k = 0; k < (int)pModel->numPackets; k++)
    {
        glModelPacket* p = (glModelPacket*)((u8*)pModel->packets + (size_t)k * sizeof(glModelPacket));
        fprintf(stderr, "GOALSPLIT model=%08x packet=%d tex %08x -> %08x\n", (unsigned)pModel->id, k, (unsigned)p->state.texture[0],
                (unsigned)spare);
        p->state.texture[0] = spare;
    }
}

static void PortFieldExtras(glModel* pModel)
{
    static const char* sOff = getenv("STRIKERS_FIELD_EXTRAS");
    if (sOff != NULL && strcmp(sOff, "0") == 0)
        return;
    const PortFieldExtra* e = NULL;
    for (size_t i = 0; i < sizeof(kPortFieldExtras) / sizeof(kPortFieldExtras[0]); i++)
    {
        if (nlStringLowerHash(kPortFieldExtras[i].name) == pModel->id)
        {
            e = &kPortFieldExtras[i];
            break;
        }
    }
    if (e == NULL)
        return;
    // newfield01 model-space bounds and instance transform (x scaled 1.5, y shifted -0.1717).
    const float xmin = -16.590908f, xmax = 16.590902f, ymin = -14.074756f, ymax = 14.519859f;
    int done = 0;
    for (int k = 0; k < (int)pModel->numPackets && k < 32; k++)
    {
        if (!(e->packetMask & (1u << k)))
            continue;
        glModelPacket* p = (glModelPacket*)((u8*)pModel->packets + (size_t)k * sizeof(glModelPacket));
        const glModelStream* pos = NULL;
        const glModelStream* uv = NULL;
        int detailIdx = -1; // plate pieces: their spare UV stream (id 7) becomes the field's detail-layer UV (id 4)
        for (int st = 0; st < (int)p->numStreams; st++)
        {
            if (p->streams[st].id == 0)
                pos = &p->streams[st];
            else if (p->streams[st].id == 3)
                uv = &p->streams[st];
            else if (p->streams[st].id == 7 && p->streams[st].stride >= 4 && e->zset < 999.0f)
                detailIdx = st;
        }
        if (pos == NULL || uv == NULL || p->indexBuffer == 0 || uv->stride < 4)
            continue;
        const u16* idx = (const u16*)p->indexBuffer;
        const bool bGrow = strncmp(e->name, "mario_stadium/netshadow", 23) == 0 || e->zset < 999.0f;
        if (bGrow)
        {
            // Grow the fill piece a hair about its own centre so it overlaps the field instead of leaving a hairline
            // crack (the dark line) along the seam. Same image on both sides, so the overlap is invisible.
            float bx0 = 1e30f, bx1 = -1e30f, by0 = 1e30f, by1 = -1e30f;
            for (int i = 0; i < (int)p->numVertices; i++)
            {
                const u8* pv = (const u8*)pos->address + (size_t)idx[i] * pos->stride;
                float x, y;
                if (pos->stride >= 12) { x = port_bef32(pv); y = port_bef32(pv + 4); }
                else { x = (float)(s16)((pv[0] << 8) | pv[1]) / 256.0f; y = (float)(s16)((pv[2] << 8) | pv[3]) / 256.0f; }
                if (x < bx0) bx0 = x;
                if (x > bx1) bx1 = x;
                if (y < by0) by0 = y;
                if (y > by1) by1 = y;
            }
            const float cx = 0.5f * (bx0 + bx1), cy = 0.5f * (by0 + by1);
            const float sxs = (bx1 - bx0) > 0.01f ? 1.0f + 0.08f / (bx1 - bx0) : 1.0f;
            const float sys = (by1 - by0) > 0.01f ? 1.0f + 0.08f / (by1 - by0) : 1.0f;
            std::set<unsigned> seen;
            for (int i = 0; i < (int)p->numVertices; i++)
            {
                if (!seen.insert((unsigned)idx[i]).second)
                    continue;
                u8* pv = (u8*)pos->address + (size_t)idx[i] * pos->stride;
                if (pos->stride >= 12)
                {
                    const float x = port_bef32(pv), y = port_bef32(pv + 4);
                    PortStoreBEf32(pv, cx + (x - cx) * sxs);
                    PortStoreBEf32(pv + 4, cy + (y - cy) * sys);
                    if (e->zset < 999.0f)
                        PortStoreBEf32(pv + 8, e->zset);
                }
                else
                {
                    const float x = (float)(s16)((pv[0] << 8) | pv[1]) / 256.0f;
                    const float y = (float)(s16)((pv[2] << 8) | pv[3]) / 256.0f;
                    int nx = (int)floorf((cx + (x - cx) * sxs) * 256.0f + 0.5f);
                    int ny = (int)floorf((cy + (y - cy) * sys) * 256.0f + 0.5f);
                    pv[0] = (u8)((nx >> 8) & 0xFF); pv[1] = (u8)(nx & 0xFF);
                    pv[2] = (u8)((ny >> 8) & 0xFF); pv[3] = (u8)(ny & 0xFF);
                    if (e->zset < 999.0f)
                    {
                        int nz = (int)floorf(e->zset * 256.0f + 0.5f);
                        pv[4] = (u8)((nz >> 8) & 0xFF); pv[5] = (u8)(nz & 0xFF);
                    }
                }
            }
        }
        for (int st = 0; st < (int)p->numStreams; st++)
        {
            // Same flat vertex colour as the field pieces, so every piece reads as the same picture.
            if (p->streams[st].id == 2 && p->streams[st].stride >= 4)
            {
                for (int i = 0; i < (int)p->numVertices; i++)
                {
                    u8* pc = (u8*)p->streams[st].address + (size_t)idx[i] * p->streams[st].stride;
                    pc[0] = 255; pc[1] = 255; pc[2] = 255; pc[3] = 255;
                }
            }
        }
        for (int i = 0; i < (int)p->numVertices; i++)
        {
            const u8* pv = (const u8*)pos->address + (size_t)idx[i] * pos->stride;
            float x, y;
            if (pos->stride >= 12)
            {
                x = port_bef32(pv);
                y = port_bef32(pv + 4);
            }
            else
            {
                x = (float)(s16)((pv[0] << 8) | pv[1]) / 256.0f;
                y = (float)(s16)((pv[2] << 8) | pv[3]) / 256.0f;
            }
            const float wx = e->sx * x + e->tx;
            const float wy = e->sy * y + e->ty;
            const float u = (wx / 1.5f - xmin) / (xmax - xmin) * 1024.0f;
            const float v = (ymax - (wy + 0.1717f)) / (ymax - ymin) * 1024.0f;
            int ui = (int)(u + (u < 0 ? -0.5f : 0.5f));
            int vi = (int)(v + (v < 0 ? -0.5f : 0.5f));
            if (ui < -32768) ui = -32768;
            if (ui > 32767) ui = 32767;
            if (vi < -32768) vi = -32768;
            if (vi > 32767) vi = 32767;
            u8* pu = (u8*)uv->address + (size_t)idx[i] * uv->stride;
            pu[0] = (u8)((ui >> 8) & 0xFF);
            pu[1] = (u8)(ui & 0xFF);
            pu[2] = (u8)((vi >> 8) & 0xFF);
            pu[3] = (u8)(vi & 0xFF);
            if (detailIdx >= 0)
            {
                // The field pieces' detail-layer UV is a plain linear function of position (fitted from the data).
                const float xm = wx / 1.5f, ym = wy + 0.1717f;
                int du = (int)floorf((0.4380f * xm + 7.2645f) * 1024.0f + 0.5f);
                int dv = (int)floorf((-0.1150f * ym - 2.7295f) * 1024.0f + 0.5f);
                u8* pd = (u8*)p->streams[detailIdx].address + (size_t)idx[i] * p->streams[detailIdx].stride;
                pd[0] = (u8)((du >> 8) & 0xFF);
                pd[1] = (u8)(du & 0xFF);
                pd[2] = (u8)((dv >> 8) & 0xFF);
                pd[3] = (u8)(dv & 0xFF);
            }
        }
        if (detailIdx >= 0)
        {
            // Same two texture stages as the field pieces (field image + shared detail layer).
            p->streams[detailIdx].id = 4;
            p->state.texturestate = 0x12b00000ULL;
            p->state.texconfig = 0x03;
            p->state.texture[1] = (uintptr_t)0x5c5698b2u;
            for (int t = 2; t < 6; t++)
                p->state.texture[t] = (uintptr_t)0xffffffffu;
        }
        p->state.texture[0] = (uintptr_t)0xf406f013u;
        if (strncmp(e->name, "mario_stadium/netshadow", 23) == 0)
        {
            // Same texture stages as the field pieces themselves: drops the net-shadow layer (and its edge line).
            p->state.texturestate = 0x12b00000ULL;
            p->state.texconfig = 0x03;
            p->state.texture[2] = (uintptr_t)0xffffffffu;
        }
        done++;
    }
    fprintf(stderr, "FIELDEXTRA model=%08x packets=%d\n", (unsigned)pModel->id, done);
}

// BMD model chunk type IDs.
enum BMDChunkType
{
    BMD_CHUNK_FILE_INFO = 0x1B001,
    BMD_CHUNK_REF_DATA = 0x1B002,
    BMD_CHUNK_MODELS = 0x1B003,
    BMD_CHUNK_PACKETS = 0x1B004,
    BMD_CHUNK_STREAMS = 0x1B005,
    BMD_CHUNK_DISPLAY_LIST = 0x1B006,
    BMD_CHUNK_INDEX_DATA = 0x1B007,
    BMD_CHUNK_SKIN = (int)0x8001B008u,
    BMD_CHUNK_TEXTURE_ANIM = 0x1B00F,
    BMD_CHUNK_VERTEX_ANIM = 0x1B011,
    BMD_CHUNK_MATERIAL_LIST = 0x1B012,
};

static const int gl_stream_stride[15] = {
    12, 3, 4, 4, 4, 4, 4, 4, 4, 12, 12, 12, 1, 16, 16
};

static void* NLVIRTUALALLOC(unsigned long size)
{
    if (nlVirtualLargestBlock() >= size + 0x100)
    {
        return nlVirtualAlloc(size, false);
    }

    OSReport("VIRTUAL MEMORY WARNING ~ NLVIRTUALALLOC had to fall back to MRAM\nLargest block: %d Total free: %d\n",
        nlVirtualLargestBlock(),
        nlVirtualTotalFree());
    return nlMalloc(size, 0x20, false);
}

// Skin mesh chunk type IDs (lower 24 bits of m_ID); switch index = (type - 0x1B009).
enum SkinChunkType
{
    SKIN_CHUNK_0x1B009 = 0x1B009,
    SKIN_CHUNK_BONE_MATRICES = 0x1B00A,
    SKIN_CHUNK_BONE_MAP_LIST = 0x1B00B,
    SKIN_CHUNK_MORPH = 0x1B00C,
    SKIN_CHUNK_SOFTWARE_VERTICES = 0x1B00D,
    SKIN_CHUNK_SKIN_PAIRS = 0x1B00E,
    SKIN_CHUNK_0x1B00F = 0x1B00F,
    SKIN_CHUNK_STITCHING = 0x1B010,
};

/**
 * Offset/Address/Size: 0xF08 | 0x801C0B28 | size: 0x8
 */
void glSetIgnoreDuplicateModels(bool ignore)
{
    glIgnoreDuplicateModels = ignore;
}

/**
 * Offset/Address/Size: 0xC08 | 0x801C0828 | size: 0x2A0
 */
GLSkinMesh* glx_MakeSkinMesh(nlChunk* outerChunk, glModel* models)
{
    ShaderSkinMesh* mesh = new (nlMalloc(sizeof(ShaderSkinMesh), 8, false)) ShaderSkinMesh();

    mesh->pModel = models;

    u32 align;
    u32 i;
    u32 count;
    nlChunk* chunkEnd = (nlChunk*)((u8*)outerChunk + outerChunk->m_Size + 8);
    u32 chunkSize;
    u8* data;

    for (nlChunk* chunk = (nlChunk*)((u8*)outerChunk + 8); chunk != chunkEnd; chunk = (nlChunk*)((u8*)chunk + chunk->m_Size + 8))
    {
        u32 id = chunk->m_ID;
        chunkSize = chunk->m_Size;
        u32 alignBits = id & 0x7F000000;
        u32 chunkType = id & ~0x7F000000u;

        u8* result;
        if (((-alignBits | alignBits) >> 31) != 0)
        {
            align = 1 << (alignBits >> 24);
            uintptr_t ptr = (uintptr_t)chunk;
            ptr += align;
            ptr += 7;
            result = (u8*)(ptr & ~(uintptr_t)(align - 1));
        }
        else
        {
            result = (u8*)chunk + 8;
        }
        data = result;

        switch (chunkType)
        {
        case 0x1B009:
            break;
        case 0x1B00A:
        {
            count = chunkSize / 0x44;
            for (i = 0; i < count; i++)
            {
                u32 boneID = *(u32*)data;
                nlMatrix4 src;
                nlMatrix4 inv;
                memcpy(&src, data + 4, sizeof(nlMatrix4));
                data += 0x44;
                nlInvertMatrix(inv, src);
                mesh->SetBoneMatrix(boneID, &inv);
            }
            break;
        }
        case 0x1B00B:
        {
            BoneMapList* node = new (nlMalloc(sizeof(BoneMapList), 8, false)) BoneMapList;

            count = chunkSize >> 3;
            node->m_next = NULL;
            for (i = 0; i < count; i++)
            {
                unsigned long key = *(u32*)(data + 0);
                unsigned long value = *(u32*)(data + 4);
                data += 8;
                node->boneMap.Add(key, value);
            }
            nlRingAddEnd<BoneMapList>(&mesh->boneMaps, node);
            break;
        }
        case 0x1B00D:
            mesh->SetSoftwareVertices((int)(chunkSize >> 4), (const SkinVertex*)data);
            break;
        case 0x1B00E:
            mesh->AppendSkinPairList((int)(chunkSize >> 2), (const SkinPair*)data);
            break;
        case 0x1B00C:
        {
            u32 numMorphs = *(u32*)(data + 0);
            mesh->numMorphs = (int)numMorphs;
            mesh->numBaseVerts = *(u32*)(data + 4);
            data += 8;
            mesh->SetMorphIDs((const u32*)data);
            data += numMorphs * 4;
            mesh->SetMorphNumDeltas((const u32*)data);
            data += numMorphs * 4;
            mesh->SetMorphDeltas(*(int*)data, (const MorphDelta*)(data + 4));
            break;
        }
        case 0x1B00F:
            break;
        case 0x1B010:
            mesh->AppendStitchingInfo(*(int*)(data + 4), *(int*)(data + 0), (int)chunkSize - 8, data + 8);
            break;
        }
    }

    mesh->StitchModel();
    return mesh;
}

/**
 * Offset/Address/Size: 0x1D0 | 0x801BFDF0 | size: 0xA38
 */
static glModel* glxLoadModelFromMemory(char* data, int size, unsigned long* pNumModels, bool bLoadTextures)
{
    // PORT: big-endian; a chunk tree bmd_endian.c refuses would be walked out of bounds.
    if (port_bmd_swap_headers(data, (unsigned long)size) == 0)
    {
        OSReport("Error: model data is not a well-formed chunk tree\n");
        return NULL;
    }

    bool hasBmdHeader = false;
    nlChunk* innerEnd;
    u8* currentOuter;
    nlChunk* outerChunkPtr;
    nlChunk* outerEnd;
    nlChunk* chunkStart;
    nlChunk* chunkEnd;
    u32 numModels;
    int numPacketEntries;
    int numStreamEntries;
    uintptr_t refDataPtr;   // PORT: an address
    glModel* pModels;
    glModelPacket* pPackets;
    u8* pStreamData;
    u8* pDisplayListData;
    u32 vertexDataSize = 0;
    u8* pIndexData;
    bool hasSkinData;
    nlChunk* chunk;

    outerChunkPtr = (nlChunk*)data;
    outerEnd = (nlChunk*)(data + size);
    chunkStart = outerChunkPtr;
    chunkEnd = outerEnd;

    if ((*(u32*)outerChunkPtr & ~0x7F000000u) == 0x8001B100u)
    {
        u32 innerSize = outerChunkPtr->m_Size;
        chunkStart = (nlChunk*)((u8*)outerChunkPtr + 8);
        chunkEnd = (nlChunk*)((u8*)outerChunkPtr + innerSize + 8);
        hasBmdHeader = true;
    }

    hasSkinData = false;

    while (chunkStart < chunkEnd)
    {
        if (hasBmdHeader)
        {
            nlChunk* topChunk = (nlChunk*)chunkStart;
            outerChunkPtr = chunkStart;
            outerEnd = (nlChunk*)((u8*)chunkStart + topChunk->m_Size + 8);
        }

        while (outerChunkPtr < outerEnd)
        {
            currentOuter = (u8*)outerChunkPtr;
            chunk = (nlChunk*)(currentOuter + 8);
            innerEnd = (nlChunk*)(currentOuter + outerChunkPtr->m_Size + 8);

            while (chunk != innerEnd)
            {
                u32 rawId = chunk->m_ID;
                u32 chunkSize = chunk->m_Size;
                u32 alignBits = rawId & 0x7F000000u;
                int id = (int)(rawId & ~0x7F000000u);
                u8* chunkData;
                if (((-alignBits | alignBits) >> 31) != 0)
                {
                    u32 align = 1u << (alignBits >> 24);
                    chunkData = (u8*)nlAlignUp((uintptr_t)(chunk + 1), align);
                }
                else
                {
                    chunkData = (u8*)chunk + 8;
                }

                switch (id)
                {
                case BMD_CHUNK_FILE_INFO:
                    break;
                case BMD_CHUNK_REF_DATA:
                {
                    void* p = glResourceAlloc(chunkSize, GLM_Matrix);
                    refDataPtr = (uintptr_t)p;
                    memcpy(p, chunkData, chunkSize);
                    // PORT: matrices, and the file is big-endian.
                    port_be32_array(p, chunkSize / 4);
                    break;
                }
                case BMD_CHUNK_MODELS:
                {
                    numModels = chunkSize >> 4;
                    if (pNumModels != NULL)
                        *pNumModels = numModels;
                    pModels = (glModel*)glResourceAlloc(
                        numModels * sizeof(glModel), GLM_Header);
                    port_bmd_convert_models(pModels, chunkData, numModels,
                                            sizeof(glModel));
                    {
                        glModel* pEnt = pModels;
                        glModel* pEntEnd = pModels + numModels;
                        for (; pEnt < pEntEnd; pEnt++)
                        {
                            if (glIgnoreDuplicateModels)
                            {
                                if (glInventory.GetModel(pEnt->id) != NULL)
                                {
                                    pEnt++;
                                    continue;
                                }
                            }
                            glInventory.AddModel(pEnt->id, pEnt);
                        }
                    }
                    break;
                }
                case BMD_CHUNK_PACKETS:
                {
                    numPacketEntries = (int)port_bmd_packet_count(chunkSize);
                    pPackets = (glModelPacket*)glResourceAlloc(
                        numPacketEntries * sizeof(glModelPacket), GLM_Header);
                    port_bmd_convert_packets(pPackets, chunkData, numPacketEntries);
                    break;
                }
                case BMD_CHUNK_STREAMS:
                {
                    numStreamEntries = (int)port_bmd_stream_count(chunkSize);
                    pStreamData = (u8*)glResourceAlloc(
                        numStreamEntries * sizeof(glModelStream), GLM_Header);
                    port_bmd_convert_streams(pStreamData, chunkData, numStreamEntries);
                    break;
                }
                case BMD_CHUNK_DISPLAY_LIST:
                {
                    vertexDataSize = chunkSize;
                    pDisplayListData = (u8*)glResourceAlloc(chunkSize, GLM_VertexData);
                    memcpy(pDisplayListData, chunkData, chunkSize);
                    DCFlushRange(pDisplayListData, chunkSize);
                    break;
                }
                case BMD_CHUNK_INDEX_DATA:
                {
                    pIndexData = (u8*)nlMalloc(chunkSize, 8, true);
                    memcpy(pIndexData, chunkData, chunkSize);
                    port_bmd_swap_indices(pIndexData, chunkSize);
                    DCFlushRange(pIndexData, chunkSize);
                    break;
                }
                case BMD_CHUNK_TEXTURE_ANIM:
                {
                    // PORT: 4-byte big-endian fields.
                    const u8* p32 = (const u8*)chunkData;
                    unsigned long canonID = port_be32(p32);
                    p32 += 4;
                    if (glInventory.GetTextureAnim(canonID) == NULL)
                    {
                        unsigned long num = port_be32(p32);
                        p32 += 4;
                        unsigned long mode = port_be32(p32);
                        p32 += 4;
                        float start = port_bef32(p32);
                        p32 += 4;
                        GLTextureAnim* pAnim = new (nlMalloc(sizeof(GLTextureAnim), 8, false)) GLTextureAnim();
                        pAnim->m_unk_0x00 = (s32)canonID;
                        pAnim->SetNumTextures(num);
                        pAnim->m_mode = mode;
                        pAnim->SetFrame((int)start);
                        unsigned long index;
                        GLAnimTex animTex;
                        for (index = 0; index < num; index++)
                        {
                            unsigned long hashID = port_be32(p32);
                            p32 += 4;
                            animTex.textureHandle = hashID;
                            animTex.time = port_bef32(p32);
                            p32 += 4;
                            pAnim->SetTexture(index, animTex);
                        }
                        glInventory.AddTextureAnim(canonID, pAnim);
                    }
                    else
                    {
                        tDebugPrintManager::Print(DC_LOADER, "skipping duplicate texanim 0x%08X\n", canonID);
                    }
                    break;
                }
                case BMD_CHUNK_VERTEX_ANIM:
                {
                    // PORT: 4-byte big-endian fields.
                    const u8* p32 = (const u8*)chunkData;
                    unsigned long hashID = port_be32(p32 + 0);
                    unsigned long numFrames = port_be32(p32 + 4);
                    unsigned long numVerts = port_be32(p32 + 8);
                    unsigned long fps = port_be32(p32 + 12);
                    p32 += 16;
                    GLVertexAnim* pAnim = new (nlMalloc(sizeof(GLVertexAnim), 8, false)) GLVertexAnim();
                    pAnim->m_uHashID = hashID;
                    pAnim->m_nNumFrames = numFrames;
                    pAnim->m_nNumVertices = numVerts;
                    pAnim->m_fFrameRate = (float)fps;
                    unsigned long size = numFrames * 12 * numVerts;
                    nlVector3* pVertices = (nlVector3*)glResourceAlloc(size, GLM_VertexData);
                    memcpy(pVertices, p32, size);
                    // PORT: and the vertices themselves are big-endian floats.
                    port_be32_array(pVertices, size / 4);
                    DCFlushRange(pVertices, size);
                    pAnim->m_pVertices = pVertices;
                    pAnim->m_pModel = glInventory.GetModel(hashID);
                    pAnim->Reset();
                    glInventory.AddVertexAnim(hashID, pAnim);
                    break;
                }
                case BMD_CHUNK_MATERIAL_LIST:
                {
                    // PORT: 4-byte big-endian fields.
                    u8* p32 = (u8*)chunkData;
                    unsigned long modelID = port_be32(p32 + 0);
                    unsigned long numMats = port_be32(p32 + 4);
                    p32 += 8;
                    // GLMaterialEntry is three u32s on both sides, so the array needs converting but not reshaping.
                    port_be32_array(p32, numMats * 3);
                    GLMaterialList* pList = new (nlMalloc(sizeof(GLMaterialList), 8, false)) GLMaterialList();
                    pList->m_uHashID = modelID;
                    pList->SetMaterials(numMats, (const GLMaterialEntry*)p32);
                    glInventory.AddMaterialList(modelID, pList);
                    break;
                }
                case BMD_CHUNK_SKIN:
                {
                    u32 skinSize = chunkSize + 8;
                    nlChunk* pSkinChunk = (nlChunk*)NLVIRTUALALLOC(skinSize);
                    memcpy(pSkinChunk, chunk, skinSize);
                    // PORT: big-endian payloads, converted once where the chunk is copied; a chunk
                    // skin_endian.c refuses would be read out of bounds, so the model has no skin data.
                    if (port_skin_swap(pSkinChunk) == 0)
                    {
                        OSReport("Error: SKIN chunk of model %lu is not well-formed; ignored\n", (unsigned long)pModels->id);
                        break;
                    }
                    // PORT: see rw_glinventory_skinprobe.
                    if (getenv("STRIKERS_PROBE_SKIN"))
                        OSReport("[skin] ADD id=%lu pModels=%p numModels=%lu\n",
                                 (unsigned long)pModels->id, (void*)pModels,
                                 (unsigned long)numModels);
                    glInventory.AddSkinData(pModels->id, pSkinChunk);
                    hasSkinData = true;
                    break;
                }
                default:
                    break;
                }

                chunk = (nlChunk*)((u8*)chunk + chunk->m_Size + 8);
            }

            outerChunkPtr = (nlChunk*)(currentOuter + outerChunkPtr->m_Size + 8);

            {
                int count = numModels;
                glModel* pM = pModels;
                while (count > 0)
                {
                    pM->packets = (glModelPacket*)((uintptr_t)pM->packets + (uintptr_t)pPackets);
                    pM++;
                    count--;
                }
            }

            {
                int i;
                glModelPacket* pPkt = pPackets;
                for (i = 0; i < numPacketEntries; i++)
                {
                    if (glGetRasterState(pPkt->state.raster, (eGLState)5) == 0)
                    {
                        if (glTextureLoad(pPkt->state.texture[0]))
                        {
                            glUnHandleizeRasterState(pPkt->state.raster);
                            int bits = glTextureGetNumBits(3);
                            if (bits == 1)
                            {
                                glSetRasterState((eGLState)5, 0);
                                glSetRasterState((eGLState)3, 1);
                                glSetRasterState((eGLState)4, 0x40);
                            }
                            else if (bits > 1)
                            {
                                glSetRasterState((eGLState)5, 1);
                                glSetRasterState((eGLState)3, 1);
                                glSetRasterState((eGLState)4, 0);
                                glSetRasterState((eGLState)1, 0);
                            }
                            pPkt->state.raster = glHandleizeRasterState();
                        }
                    }
                    pPkt->streams = (glModelStream*)((uintptr_t)pPkt->streams + (uintptr_t)pStreamData);
                    pPkt->indexBuffer += (uintptr_t)pIndexData;
                    pPkt->state.matrix += refDataPtr;
                    pPkt = (glModelPacket*)((u8*)pPkt + sizeof(glModelPacket));
                }
            }

            {
                // PORT: was `*(u32*)p += ...; p += 6`, glModelStream's on-disc layout.
                glModelStream* pStream = (glModelStream*)pStreamData;
                // PORT: while the addresses are still offsets.
                port_bmd_stream_sizes(pStream, numStreamEntries, vertexDataSize);
                for (int count = 0; count < numStreamEntries; count++)
                {
                    pStream[count].address += (uintptr_t)pDisplayListData;
                }
            }

            {
                glModel* pModel = pModels;
                // PORT: was bounded by numModels shifted left 4, glModel's size on disc; the host record is wider.
                glModel* pModelEnd = pModels + numModels;
                while (pModel < pModelEnd)
                {
                    PortPitchUnify(pModel);
                    PortRingPlates(pModel);
                    PortFieldExtras(pModel);
                    PortVentCover(pModel);
                    PortFieldNeutral(pModel);
                    PortGoalSplit(pModel);
                    PortHidePackets(pModel);
                    PortGoalFix(pModel);
                    PortSignOrient(pModel);
                    PortBackWallMirror(pModel);
                    glModelPacket* pPacket = pModel->packets;
                    while (pPacket < pModel->packets + pModel->numPackets)
                    {
                        if (hasSkinData)
                        {
                            if (glGetRasterState(pPacket->state.raster, (eGLState)8) == 1)
                            {
                                int oldNumStreams = pPacket->numStreams;
                                int newNum = oldNumStreams + 1;
                                glModelStream* streams = (glModelStream*)glResourceAlloc(newNum * sizeof(glModelStream), GLM_Header);
                                memcpy(streams, pPacket->streams, oldNumStreams * sizeof(glModelStream));
                                streams[oldNumStreams].id = 12;
                                streams[oldNumStreams].address = 0;
                                streams[oldNumStreams].stride = (u8)gl_stream_stride[12];
                                pPacket->numStreams = (u8)(pPacket->numStreams + 1);
                                pPacket->streams = streams;
                            }
                        }
                        if (pPacket->indexBuffer != 0)
                        {
                            pPacket->indexBuffer = (uintptr_t)dlMakeDisplayList(pPacket, true);
                        }
                        if (bLoadTextures)
                        {
                            for (int s = 0; s < 6; s++)
                            {
                                if (pPacket->state.texconfig & (1 << s))
                                {
                                    uintptr_t texHandle = pPacket->state.texture[s];
                                    // PORT: a fallback reported at draw time is just a hash; here it can still be tied to the model that asked for it.
                                    {
                                        static const bool bProbe = getenv("STRIKERS_PROBE_TEX") != NULL;
                                        if (bProbe && !glTextureLoad(texHandle))
                                        {
                                            static u32 seen[64];
                                            static int nSeen = 0;
                                            bool bNew = true;
                                            for (int q = 0; q < nSeen; q++)
                                                if (seen[q] == texHandle)
                                                    bNew = false;
                                            if (bNew && nSeen < 64)
                                            {
                                                seen[nSeen++] = texHandle;
                                                OSReport("[texload] model id 0x%08x wants texture "
                                                         "0x%08x (stage %d), not loaded\n",
                                                         (unsigned)pModel->id,
                                                         (unsigned)texHandle, s);
                                            }
                                        }
                                    }
                                    if (glInventory.GetTextureAnim(texHandle) == NULL)
                                    {
                                        if (glTextureLoad(texHandle))
                                        {
                                            pPacket->state.texture[s] = (uintptr_t)glx_GetTex(texHandle, true, true);
                                        }
                                    }
                                }
                            }
                        }
                        pPacket = (glModelPacket*)((u8*)pPacket + sizeof(glModelPacket));
                    }
                    pModel++;
                }
                nlFree(pIndexData);
            }
        }

        if (!hasBmdHeader)
            break;

        {
            nlChunk* topChunk = (nlChunk*)chunkStart;
            chunkStart = (nlChunk*)((u8*)chunkStart + topChunk->m_Size + 8);
        }
    }

    nlFree(data);
    return pModels;
}

static glModel* glxLoadModelFromDisk(const char* filename, unsigned long* pNumModels)
{
    unsigned int alignSize;
    unsigned int fileSize;
    char fullname[256];
    glModel* retval;
    nlFile* f;

    glx_FreeMemory0();
    nlStrNCat(fullname, "art/", filename, 256);

    f = nlOpen(fullname);
    if (f == NULL)
    {
        retval = NULL;
    }
    else
    {
        fileSize = nlFileSize(f, &alignSize);
        nlClose(f);
        if (fileSize == 0)
        {
            retval = NULL;
        }
        else
        {
            char* data = (char*)nlLoadEntireFileToVirtualMemory(fullname, (int*)&fileSize, 0x80000, NULL, AllocateEnd);
            if (data == NULL)
            {
                retval = NULL;
            }
            else
            {
                retval = glxLoadModelFromMemory(data, fileSize, pNumModels, true);
            }
        }
    }

    glx_FreeMemory1(filename);
    return retval;
}

/**
 * Offset/Address/Size: 0xCC | 0x801BFCEC | size: 0x104
 */
glModel* glplatLoadModel(const char* filename, unsigned long* pNumModels)
{
    unsigned int alignSize;
    unsigned int fileSize;
    char fullname[256];
    char lowerName[256];
    glModel* retval;
    nlFile* f;
    bool bSkinned;

    glx_FreeMemory0();
    nlStrNCat(fullname, "art/", filename, 256);
    nlStrNCpy(lowerName, fullname, 256);
    nlToLower(lowerName);

    bSkinned = (strstr(lowerName, "characters") == NULL);

    f = nlOpen(fullname);
    if (f == NULL)
    {
        retval = NULL;
    }
    else
    {
        fileSize = nlFileSize(f, &alignSize);
        nlClose(f);
        if (fileSize == 0)
        {
            retval = NULL;
        }
        else
        {
            char* data = (char*)nlLoadEntireFileToVirtualMemory(fullname, (int*)&fileSize, 0x80000, NULL, AllocateEnd);
            retval = glxLoadModelFromMemory(data, fileSize, pNumModels, bSkinned);
        }
    }

    glx_FreeMemory1(filename);
    return retval;
}

/**
 * Offset/Address/Size: 0x24 | 0x801BFC44 | size: 0xA8
 */
bool glplatBeginLoadModel(const char* filename, void (*callback)(void*, unsigned long, void*), void* userData)
{
    char fullname[256];
    nlStrNCat(fullname, "art/", filename, 256);

    if (userData == NULL)
    {
        if (!nlLoadEntireFileAsync(fullname, callback, userData, 32, AllocateEnd))
        {
            return false;
        }
    }
    else
    {
        if (!nlLoadEntireFileAsync(fullname, callback, userData, 32, (eAllocType)23))
        {
            return false;
        }
    }
    return true;
}

/**
 * Offset/Address/Size: 0x0 | 0x801BFC20 | size: 0x24
 */
glModel* glplatEndLoadModel(void* data, unsigned long size, unsigned long* pNumModels)
{
    return glxLoadModelFromMemory((char*)data, size, pNumModels, false);
}
