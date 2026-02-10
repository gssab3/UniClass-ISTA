package it.unisa.uniclass.utenti.controller;

import it.unisa.uniclass.common.security.CredentialSecurity;
import it.unisa.uniclass.common.security.PasswordGenerator;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.UserDirectory; // USIAMO L'INTERFACCIA
import jakarta.ejb.EJB;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import java.io.IOException;

@WebServlet(name = "AttivaUtentiServlet", value = "/AttivaUtentiServlet")
public class AttivaUtentiServlet extends HttpServlet {

    @EJB
    private UserDirectory userDirectory;

    @Override
    protected void doPost(HttpServletRequest req, HttpServletResponse resp) {
        try {
            String param = req.getParameter("param");

            if ("add".equals(param)) {
                String email = req.getParameter("email");
                String matricola = req.getParameter("matricola");
                String ruoloReq = req.getParameter("tipo"); // Stringa dalla view (es. "STUDENTE")

                Utente utente = userDirectory.getUser(email);

                if (utente instanceof Accademico) {
                    Accademico acc = (Accademico) utente;

                    // Verifica corrispondenza Ruolo (Case insensitive)
                    boolean ruoloMatch = acc.getRuolo() != null &&
                            acc.getRuolo().toString().equalsIgnoreCase(ruoloReq);

                    // Verifica Matricola e Ruolo
                    if (acc.getMatricola() != null && acc.getMatricola().equals(matricola) && ruoloMatch) {
                        String password = PasswordGenerator.generatePassword(8);

                        acc.setAttivato(true);
                        acc.setPassword(CredentialSecurity.hashPassword(password));

                        // Aggiornamento tramite Facade
                        userDirectory.updateProfile(acc);

                        System.out.println("Utente attivato: " + email + " Pwd: " + password);
                        resp.sendRedirect(req.getContextPath() + "/PersonaleTA/AttivaUtenti.jsp");
                    } else {
                        resp.sendRedirect(req.getContextPath() + "/PersonaleTA/AttivaUtenti.jsp?action=error");
                    }
                } else {
                    resp.sendRedirect(req.getContextPath() + "/PersonaleTA/AttivaUtenti.jsp?action=error");
                }

            } else if ("remove".equals(param)) {
                String email = req.getParameter("email-remove");
                Utente utente = userDirectory.getUser(email);

                if (utente instanceof Accademico) {
                    Accademico acc = (Accademico) utente;
                    acc.setAttivato(false);
                    userDirectory.updateProfile(acc);
                }
                resp.sendRedirect(req.getContextPath() + "/PersonaleTA/AttivaUtenti.jsp");
            }
        } catch (Exception e) {
            req.getServletContext().log("Error processing user activation", e);
            try {
                resp.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
            } catch (IOException ignored) {}
        }
    }

    @Override
    protected void doGet(HttpServletRequest req, HttpServletResponse resp) {
        doPost(req, resp);
    }
}