package it.unisa.uniclass.utenti.controller;

import it.unisa.uniclass.common.security.CSRF;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;

import java.io.IOException;

@WebServlet(name = "LogoutServlet", value = "/LogoutServlet")
public class LogoutServlet extends HttpServlet {
    private static final long serialVersionUID = 1L;

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) {
        try {
            response.sendError(HttpServletResponse.SC_METHOD_NOT_ALLOWED);
        } catch (IOException ignored) {}
    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) {
        try {
            if (!CSRF.isValid(request)) {
                response.sendError(HttpServletResponse.SC_FORBIDDEN);
                return;
            }
            HttpSession session = request.getSession(false);
            if (session != null) {
                session.invalidate();
                request.getServletContext().log("Sessione invalidata con successo per l'utente.");
            }
            response.sendRedirect(request.getContextPath() + "/Home");
        } catch (Exception e) {
            request.getServletContext().log("ERRORE CRITICO durante il logout", e);
            try {
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
            } catch (IOException ignored) {}
        }
    }
}
