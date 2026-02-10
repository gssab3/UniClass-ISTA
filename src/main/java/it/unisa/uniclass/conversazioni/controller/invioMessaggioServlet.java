package it.unisa.uniclass.conversazioni.controller;

import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.model.Topic;
import it.unisa.uniclass.conversazioni.service.MessaggioService;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.service.UserDirectory; // INTERFACCIA
import jakarta.ejb.EJB;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;

import java.io.IOException;
import java.time.LocalDateTime;
import java.util.List;

@WebServlet(name = "invioMessaggio", value = "/invioMessaggioServlet")
public class invioMessaggioServlet extends HttpServlet {

    @EJB
    private MessaggioService messaggioService;

    @EJB
    private UserDirectory userDirectory;

    @Override
    public void doGet(HttpServletRequest request, HttpServletResponse response) {
        try {
            HttpSession session = request.getSession();

            String emailSession = (String) session.getAttribute("utenteEmail");
            String emailDest = request.getParameter("email");
            String messaggioBody = request.getParameter("testo");
            String topic = request.getParameter("topic");

            Accademico accademicoSelf = userDirectory.getAccademico(emailSession);
            Accademico accademicoDest = userDirectory.getAccademico(emailDest);

            if (accademicoSelf != null && accademicoDest != null) {
                Messaggio messaggio1 = new Messaggio();
                messaggio1.setAutore(accademicoSelf);
                messaggio1.setDestinatario(accademicoDest);
                messaggio1.setBody(messaggioBody);
                messaggio1.setDateTime(LocalDateTime.now());

                if (topic != null && !topic.isEmpty()) {
                    Topic top = new Topic();
                    top.setNome(topic);
                    top.setCorsoLaurea(accademicoSelf.getCorsoLaurea());
                    messaggio1.setTopic(top);
                }

                messaggioService.aggiungiMessaggio(messaggio1);

                List<Messaggio> messaggi = messaggioService.trovaTutti();
                request.setAttribute("messaggi", messaggi);
                request.setAttribute("accademici", messaggioService.trovaMessaggeriDiUnAccademico(accademicoSelf.getMatricola()));

                response.sendRedirect("Conversazioni");
            } else {
                throw new ServletException("Errore nel recupero degli utenti per l'invio.");
            }

        } catch (Exception e) {
            request.getServletContext().log("Error sending message", e);
            try {
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
            } catch (IOException ignored) {}
        }
    }

    @Override
    public void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        doGet(request, response);
    }
}