package it.unisa.uniclass.common.security;

import it.unisa.uniclass.utenti.model.Tipo;
import it.unisa.uniclass.utenti.model.Utente;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import java.io.IOException;

public class Authorization {
    public static Utente require(HttpServletRequest req, HttpServletResponse resp, Tipo... allowed) throws IOException {
        HttpSession session = req.getSession(false);
        Utente user = null;
        if (session != null) {
            Object value = session.getAttribute("currentSessionUser");
            if (value instanceof Utente) {
                user = (Utente) value;
            }
        }
        if (user == null) {
            resp.sendError(HttpServletResponse.SC_UNAUTHORIZED);
            return null;
        }
        for (Tipo tipo : allowed) {
            if (user.getTipo() == tipo) {
                return user;
            }
        }
        resp.sendError(HttpServletResponse.SC_FORBIDDEN);
        return null;
    }
}
