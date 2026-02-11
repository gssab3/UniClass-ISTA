package it.unisa.uniclass.utenti.controller;

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
            // 1. Recupera la sessione senza crearne una nuova
            HttpSession session = request.getSession(false);

            // 2. Se la sessione esiste, invalidala
            if (session != null) {
                session.invalidate();
                request.getServletContext().log("Sessione invalidata con successo per l'utente.");
            }

            // 3. (Opzionale) Se usi il Login di Tomcat/Container, decommenta questa riga:
            // request.logout();

            // 4. Redirect verso la Home
            // Usa il contesto dinamico per evitare problemi di path
            response.sendRedirect(request.getContextPath() + "/Home");

        } catch (Exception e) {
            // Cattura QUALSIASI eccezione (anche NullPointerException)
            request.getServletContext().log("ERRORE CRITICO durante il logout", e);
            e.printStackTrace(); // Stampa nello standard output (visibile nei log di Docker)

            try {
                // Invia un errore leggibile al client invece di una pagina bianca
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR, "Logout fallito: " + e.getMessage());
            } catch (IOException ioException) {
                ioException.printStackTrace();
            }
        }
    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) {
        doGet(request, response);
    }
}