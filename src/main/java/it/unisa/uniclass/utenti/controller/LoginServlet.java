package it.unisa.uniclass.utenti.controller;

import it.unisa.uniclass.common.exceptions.AuthenticationException;
import it.unisa.uniclass.common.security.CredentialSecurity;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.UtenteService;
import jakarta.ejb.EJB;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;

import java.io.IOException;

@WebServlet(name = "loginServlet", value = "/Login")
public class LoginServlet extends HttpServlet {

    @EJB
    private UtenteService utenteService;

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) {
        doPost(request, response);
    }

    @Override
    public void doPost(HttpServletRequest request, HttpServletResponse response) {
        try {
            String email = request.getParameter("email");
            String passwordRaw = request.getParameter("password");

            // Hash della password (se il DB contiene password hashate)
            String password = CredentialSecurity.hashPassword(passwordRaw);

            try {
                // Unico punto di accesso per il login
                Utente user = utenteService.login(email, password);

                // Controllo specifico per Accademici (devono essere attivati)
                if (user instanceof Accademico) {
                    Accademico acc = (Accademico) user;
                    if (!acc.isAttivato()) {
                        response.sendRedirect(request.getContextPath() + "/Login.jsp?action=notactivated");
                        return;
                    }
                }

                // Login successo
                HttpSession session = request.getSession(true);
                session.setAttribute("currentSessionUser", user);
                // Salviamo anche l'email per compatibilità con altre servlet vecchie
                session.setAttribute("utenteEmail", user.getEmail());

                response.sendRedirect(request.getContextPath() + "/Home");

            } catch (AuthenticationException e) {
                // Credenziali errate
                response.sendRedirect(request.getContextPath() + "/Login.jsp?action=error");
            }

        } catch (IOException e) {
            request.getServletContext().log("Error processing login request", e);
            try {
                response.sendRedirect(request.getContextPath() + "/Login.jsp?action=error");
            } catch (IOException ioException) {
                // ignore
            }
        }
    }
}