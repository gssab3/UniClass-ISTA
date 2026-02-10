package it.unisa.uniclass.conversazioni.service;

import it.unisa.uniclass.common.exceptions.NotFoundUserException;
import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.model.Topic;
import it.unisa.uniclass.conversazioni.service.dao.MessaggioRemote;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.UserDirectory; // INTERFACCIA
import jakarta.ejb.EJB;
import jakarta.ejb.LocalBean;
import jakarta.ejb.Stateless;
import jakarta.persistence.NoResultException;

import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;

@Stateless
@LocalBean
public class MessaggioService {

    @EJB(beanName = "MessaggioDAO")
    private MessaggioRemote messaggioDao;

    // SOSTITUZIONE: Dipendenza verso l'interfaccia Facade
    @EJB
    private UserDirectory userDirectory;

    public MessaggioService() {
    }

    public void inviaMessaggio(String testo, String emailAutore, String emailDestinatario) throws Exception {
        // Uso UserDirectory per recuperare gli utenti
        Utente uMittente = userDirectory.getUser(emailAutore);
        Utente uDestinatario = userDirectory.getUser(emailDestinatario);

        if (!(uMittente instanceof Accademico)) {
            throw new IllegalArgumentException("Il mittente non è abilitato all'invio di messaggi accademici.");
        }
        if (!(uDestinatario instanceof Accademico)) {
            throw new IllegalArgumentException("Il destinatario non è un utente accademico valido.");
        }

        Messaggio msg = new Messaggio();
        msg.setBody(testo);
        msg.setAutore((Accademico) uMittente);
        msg.setDestinatario((Accademico) uDestinatario);
        msg.setDateTime(LocalDateTime.now());

        messaggioDao.aggiungiMessaggio(msg);
    }

    public Messaggio trovaMessaggio(long id) {
        try {
            return messaggioDao.trovaMessaggio(id);
        } catch (NoResultException e) {
            return null;
        }
    }

    public List<Messaggio> trovaMessaggiInviati(String matricola) {
        return messaggioDao.trovaMessaggiInviati(matricola);
    }

    public List<Messaggio> trovaMessaggiRicevuti(String matricola) {
        return messaggioDao.trovaMessaggiRicevuti(matricola);
    }

    public List<Messaggio> trovaMessaggi(String matricola1, String matricola2) {
        return messaggioDao.trovaMessaggi(matricola1, matricola2);
    }

    public List<Messaggio> trovaTutti() {
        return messaggioDao.trovaTutti();
    }

    public List<Messaggio> trovaAvvisi() {
        return messaggioDao.trovaAvvisi();
    }

    public List<Messaggio> trovaAvvisiAutore(String autore) {
        return messaggioDao.trovaAvvisiAutore(autore);
    }

    public List<Messaggio> trovaMessaggiData(LocalDateTime dateTime) {
        return messaggioDao.trovaMessaggiData(dateTime);
    }

    public List<Accademico> trovaMessaggeriDiUnAccademico(String matricola) {
        List<Messaggio> messaggi = messaggioDao.trovaMessaggiRicevuti(matricola);
        List<Accademico> mittenti = new ArrayList<>();
        for (Messaggio messaggio : messaggi) {
            if (messaggio.getAutore() != null && !mittenti.contains(messaggio.getAutore())) {
                mittenti.add(messaggio.getAutore());
            }
        }
        return mittenti;
    }

    public List<Messaggio> trovaTopic(Topic topic) {
        return messaggioDao.trovaTopic(topic);
    }

    public Messaggio aggiungiMessaggio(Messaggio messaggio) {
        if (messaggio != null) {
            return messaggioDao.aggiungiMessaggio(messaggio);
        }
        return null;
    }

    public void rimuoviMessaggio(Messaggio messaggio) {
        if (messaggio != null) {
            messaggioDao.rimuoviMessaggio(messaggio);
        }
    }
}