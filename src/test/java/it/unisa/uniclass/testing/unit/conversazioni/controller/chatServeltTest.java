package it.unisa.uniclass.testing.unit.conversazioni.controller;

import it.unisa.uniclass.conversazioni.controller.chatServlet;
import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.model.Topic;
import it.unisa.uniclass.conversazioni.service.MessaggioService;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.service.UserDirectory;
import jakarta.servlet.ServletContext;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.io.IOException;
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.List;

import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class ChatServletTest {

    private chatServlet servlet;

    @Mock private HttpServletRequest request;
    @Mock private HttpServletResponse response;
    @Mock private HttpSession session;
    @Mock private ServletContext servletContext;
    @Mock private MessaggioService messaggioService;
    @Mock private UserDirectory userDirectory;

    @BeforeEach
    void setUp() throws Exception {
        servlet = new chatServlet();

        // Inject EJB
        Field msgField = chatServlet.class.getDeclaredField("messaggioService");
        msgField.setAccessible(true);
        msgField.set(servlet, messaggioService);

        Field userField = chatServlet.class.getDeclaredField("userDirectory");
        userField.setAccessible(true);
        userField.set(servlet, userDirectory);

        lenient().when(request.getSession()).thenReturn(session);
        lenient().when(request.getServletContext()).thenReturn(servletContext);
        lenient().when(request.getContextPath()).thenReturn("/ctx");
    }

    @Test
    @DisplayName("DoGet: Successo - Filtraggio messaggi inviati/ricevuti e Lazy Load")
    void testDoGet_Success_WithFiltering() throws IOException {
        // 1. Arrange Data
        String selfEmail = "me@unisa.it";
        String selfMatr = "111";
        String destEmail = "other@unisa.it";

        when(request.getParameter("accademico")).thenReturn(destEmail);
        when(request.getParameter("accademicoSelf")).thenReturn(selfEmail);

        Accademico self = mock(Accademico.class);
        when(self.getMatricola()).thenReturn(selfMatr);
        when(self.getEmail()).thenReturn(selfEmail);

        Accademico dest = mock(Accademico.class);
        when(dest.getEmail()).thenReturn(destEmail);

        when(userDirectory.getAccademico(selfEmail)).thenReturn(self);
        when(userDirectory.getAccademico(destEmail)).thenReturn(dest);

        // 2. Arrange Messages (Branch Coverage Logic)
        List<Messaggio> allMessages = new ArrayList<>();

        // Msg 1: Ricevuto dall'utente (Destinatario == Self)
        Messaggio msgRicevuto = new Messaggio();
        msgRicevuto.setDestinatario(self); // self ha matricola 111
        msgRicevuto.setAutore(dest);
        msgRicevuto.setTopic(new Topic()); // Per lazy load test
        allMessages.add(msgRicevuto);

        // Msg 2: Inviato dall'utente (Autore == Self)
        Messaggio msgInviato = new Messaggio();
        msgInviato.setDestinatario(dest);
        msgInviato.setAutore(self); // self ha matricola 111
        allMessages.add(msgInviato);

        // Msg 3: Irrilevante (né autore né dest sono self)
        Messaggio msgOther = new Messaggio();
        Accademico stranger = mock(Accademico.class);
        when(stranger.getMatricola()).thenReturn("999");
        msgOther.setAutore(stranger);
        msgOther.setDestinatario(stranger);
        allMessages.add(msgOther);

        when(messaggioService.trovaTutti()).thenReturn(allMessages);

        // 3. Act
        servlet.doGet(request, response);

        // 4. Assert
        // Verifica che le liste siano state popolate correttamente in sessione/request
        verify(request).setAttribute(eq("messaggiInviati"), argThat(list -> ((List)list).contains(msgInviato) && ((List)list).size() == 1));
        verify(request).setAttribute(eq("messaggiRicevuti"), argThat(list -> ((List)list).contains(msgRicevuto) && ((List)list).size() == 1));

        // Verifica redirect
        verify(response).sendRedirect("/ctx/chat.jsp");

        // Verifica Lazy Load calls (assicura che il loop di fix sia stato eseguito)
        verify(self, atLeastOnce()).getNome();
    }

    @Test
    @DisplayName("DoGet: Fallimento - Utenti null")
    void testDoGet_InvalidUsers() throws IOException {
        when(request.getParameter("accademico")).thenReturn("a");
        when(request.getParameter("accademicoSelf")).thenReturn("b");

        when(userDirectory.getAccademico(anyString())).thenReturn(null);

        servlet.doGet(request, response);

        verify(response).sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
        verify(servletContext).log(anyString(), any(ServletException.class));
    }

    @Test
    @DisplayName("DoGet: Branch Coverage sui null nel loop Lazy Load")
    void testDoGet_LazyLoading_NullChecks() throws IOException {
        // Arrange users
        Accademico self = new Accademico(); self.setMatricola("1");
        Accademico dest = new Accademico(); dest.setMatricola("2");

        when(userDirectory.getAccademico(any())).thenReturn(self); // Ritorna sempre self per semplicità

        // Arrange Message con campi NULL per testare i rami "if (m.getAutore() != null)" etc.
        Messaggio msgBroken = new Messaggio();
        msgBroken.setAutore(null);
        msgBroken.setDestinatario(null);
        msgBroken.setTopic(null);

        List<Messaggio> list = new ArrayList<>();
        list.add(msgBroken);

        when(messaggioService.trovaTutti()).thenReturn(list);

        // Act
        servlet.doGet(request, response);

        // Assert - Se non lancia eccezioni, i null check funzionano
        verify(response).sendRedirect(anyString());
    }

    @Test
    @DisplayName("DoPost: Delega a DoGet")
    void testDoPost() throws ServletException, IOException {
        when(request.getParameter(any())).thenReturn(null);
        when(userDirectory.getAccademico(any())).thenThrow(new RuntimeException("Delegated"));

        servlet.doPost(request, response);

        verify(servletContext).log(anyString(), any(RuntimeException.class));
    }
}